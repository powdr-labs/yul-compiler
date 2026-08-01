import YulEvmCompiler.SsaCfg.Spec.Ir
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYul

**Construction**: Yul → `yul-ssa-cfg`.

Structured SSA construction in the spirit of Braun et al. (CC 2013),
specialized to Yul's structured control flow, so no dominance frontiers and
no block sealing are ever needed: the AST walk knows every join point —

* `if c { body }` — the join block takes one parameter per in-scope variable
  the body modifies; the false edge passes the current values, the body's
  fall-through edge passes the body-end values.
* `switch` — scrutinee evaluated once into an SSA value, then a chain of
  `eq`-test blocks (two-way branches only, following solc's SSA CFG, which
  also lowers `switch` at construction); all case bodies join at one block
  parameterized by the union of their modified variable sets.
* `for` — a header block (one parameter per loop-modified variable)
  re-evaluates the condition each iteration; `body → post → header` back
  edge; dedicated `post` and `exit` blocks with their own parameters so
  `continue`/`break` edges can carry values from mid-body.
* `break`/`continue`/`leave` — jumps (resp. `ret`) carrying current values;
  the enclosing loop context records the target blocks and their variable
  sets.
* functions — separate SSA `Func`s (Yul functions cannot see caller
  locals); return variables are zero-initialized `const`s at entry and
  `ret` reads their current definitions (matching `bindZeros` and the
  `callOk` rule's `VEnv.get Vend r |>.getD 0`).

The variable environment is a scoped association list mirroring `VEnv`
exactly (`let` prepends, assignment updates the first occurrence, scope exit
drops). **Shadowing declarations are rejected** (`letDecl` of a currently
visible name): Yul itself forbids shadowing, the strict-assembly validator
enforces it, and rejecting it here means an identifier lookup is unambiguous
at every program point — which keeps non-local edges (`break`/`continue`/
`leave`) simple. Rejection is never miscompilation.

The modified-variable analysis (`modStmts`) is a sound *over*-approximation:
extra join parameters are harmless (both edges pass the same value; the
copy-propagation pass removes them), missing ones would be unsound — so the
analysis is deliberately syntactic and conservative, skipping only `funDef`
bodies (which cannot touch outer variables).

Function definitions are translated **at their statement position** (the
structural-recursion-friendly choice, like the classic backend), but a
statement list keeps translating its `funDef`s even after an unconditional
terminator (`diverted` mode): hoisting makes a function callable *before*
its definition statement, so a `f() revert(...) function f() {...}` list
still needs `f`'s body.
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics (Ident Literal Expr Stmt)
open YulSemantics.EVM (U256 Op)

/-- The construction-time variable environment: `Ident → ValId`, scoped
exactly like `VEnv` (innermost first; `set` updates the first occurrence). -/
abbrev VMap := List (Ident × ValId)

namespace VMap

def get (m : VMap) (x : Ident) : Option ValId :=
  (m.find? (·.1 = x)).map (·.2)

def set : VMap → Ident → ValId → VMap
  | [], _, _ => []
  | (y, w) :: rest, x, v =>
    if y = x then (x, v) :: rest else (y, w) :: set rest x v

def setMany (m : VMap) (xs : List Ident) (vs : List ValId) : VMap :=
  (xs.zip vs).foldl (fun acc p => acc.set p.1 p.2) m

/-- Whether `x` is currently visible (used for the no-shadowing rejection). -/
def mem (m : VMap) (x : Ident) : Bool := m.any (·.1 = x)

end VMap

/-- The loop context: `break`/`continue` targets and the variable set whose
current values their edges carry (the loop's modified-variable set `X`). -/
structure LoopCtx where
  brkTgt : BlockId
  contTgt : BlockId
  vars : List Ident

/-! ## The modified-variables analysis -/

/-- Top-level `let` declarations of a statement list (used for `for`-init
scoping). -/
def declsOf (ss : List (Stmt Op)) : List Ident :=
  ss.flatMap fun s =>
    match s with
    | .letDecl vars _ => vars
    | _ => []

mutual

/-- Identifiers assigned by `s` that are not declared by `s` itself
(assignments inside `funDef` bodies never touch outer variables and are
skipped). `locals` accumulates the names declared so far in the enclosing
list. -/
def modStmt (locals : List Ident) : Stmt Op → List Ident
  | .block body => modStmts locals body
  | .funDef _ _ _ _ => []
  | .letDecl _ _ => []
  | .assign vars _ => vars.filter (fun v => !locals.contains v)
  | .cond _ body => modStmts locals body
  | .switch _ cases dflt =>
    modCases locals cases ++ (match dflt with
      | some b => modStmts locals b
      | none => [])
  | .forLoop init _ post body =>
    modStmts locals init
      ++ modStmts (declsOf init ++ locals) post
      ++ modStmts (declsOf init ++ locals) body
  | .exprStmt _ => []
  | .«break» => []
  | .«continue» => []
  | .leave => []

/-- `modStmt` over a list, threading the locally declared names. -/
def modStmts (locals : List Ident) : List (Stmt Op) → List Ident
  | [] => []
  | s :: rest =>
    modStmt locals s ++
      (match s with
       | .letDecl vars _ => modStmts (vars ++ locals) rest
       | _ => modStmts locals rest)

/-- `modStmts` over switch case bodies. -/
def modCases (locals : List Ident) : List (Literal × List (Stmt Op)) → List Ident
  | [] => []
  | (_, b) :: rest => modStmts locals b ++ modCases locals rest

end

/-- The in-scope variables (in environment order, first occurrence only)
modified by any of `bodies`. This is the join/loop parameter set `X`. -/
def modifiedX (env : VMap) (bodies : List (List (Stmt Op))) : List Ident :=
  let mods := bodies.flatMap (modStmts [])
  ((env.map Prod.fst).eraseDups).filter mods.contains

/-! ## The builder monad -/

/-- Per-function build state: the block array under construction, the
current block id, its reversed instruction list, and the value counter. -/
structure FnState where
  blocks : Array Block := #[]
  curId : BlockId := 0
  cur : List Instr := []
  nextVal : ValId := 0

/-- Global build state: the current function plus the program-wide function
slots (allocated at scope entry, filled at the `funDef` statement). -/
structure BState where
  fn : FnState := {}
  funcs : Array (Option Func) := #[]

/-- The construction monad: state + rejection. -/
abbrev M := StateT BState Option

/-- Reject (unsupported or ill-formed input). -/
def reject {α} : M α := fun _ => none

/-- Lift an `Option` (rejecting on `none`). -/
def liftO {α} : Option α → M α
  | some a => pure a
  | none => reject

def freshVal : M ValId := fun s =>
  some (s.fn.nextVal, { s with fn := { s.fn with nextVal := s.fn.nextVal + 1 } })

def emit (i : Instr) : M Unit := fun s =>
  some ((), { s with fn := { s.fn with cur := i :: s.fn.cur } })

/-- Reserve a new block with the given parameters (body filled on `seal`). -/
def newBlock (params : List ValId) : M BlockId := fun s =>
  some (s.fn.blocks.size,
    { s with fn := { s.fn with blocks := s.fn.blocks.push ⟨params, [], .ret []⟩ } })

/-- Seal the current block with terminator `t`. -/
def sealCur (t : Term) : M Unit := fun s =>
  match s.fn.blocks[s.fn.curId]? with
  | some b =>
    some ((), { s with fn := { s.fn with
      blocks := s.fn.blocks.set! s.fn.curId ⟨b.params, s.fn.cur.reverse, t⟩,
      cur := [] } })
  | none => none

/-- Make `b` the current (empty, unsealed) block. -/
def moveTo (b : BlockId) : M Unit := fun s =>
  some ((), { s with fn := { s.fn with curId := b, cur := [] } })

/-- Read the per-function build state (for save/restore around `trFunc`). -/
def getFn : M FnState := fun s => some (s.fn, s)

/-- Replace the per-function build state. -/
def setFn (fn : FnState) : M Unit := fun s => some ((), { s with fn })

/-- Allocate a function slot; returns its `FuncId`. -/
def allocFunc : M FuncId := fun s =>
  some (s.funcs.size, { s with funcs := s.funcs.push none })

/-- Fill a previously allocated function slot. -/
def fillFunc (fid : FuncId) (f : Func) : M Unit := fun s =>
  if h : fid < s.funcs.size then
    some ((), { s with funcs := s.funcs.set fid (some f) })
  else none

/-- Function-scope stack: name → `FuncId`, innermost scope first (mirrors
`FunEnv`/`lookupFun`). -/
abbrev FMap := List (List (Ident × FuncId))

def FMap.get (fenv : FMap) (x : Ident) : Option FuncId :=
  match fenv with
  | [] => none
  | scope :: rest =>
    match (scope.find? (·.1 = x)).map (·.2) with
    | some f => some f
    | none => FMap.get rest x

/-- Allocate slots for a statement list's `funDef`s (the hoisted scope). -/
def allocScope (ss : List (Stmt Op)) : M (List (Ident × FuncId)) :=
  ss.foldlM (init := []) fun acc s =>
    match s with
    | .funDef n _ _ _ => do
      let fid ← allocFunc
      pure (acc ++ [(n, fid)])
    | _ => pure acc

/-- The always-halting builtins that terminate a block (`Term.halt`). -/
def isHaltingOp : Op → Bool
  | .stop | .ret | .revert | .invalid | .selfdestruct => true
  | _ => false

/-- Look up the current values of `xs` (edge arguments). Unambiguous because
shadowing is rejected. -/
def edgeArgs (env : VMap) (xs : List Ident) : M (List ValId) :=
  liftO (xs.mapM env.get)

/-! ## The translation -/

mutual

/-- Translate an expression to a single SSA value. -/
def trExpr (fenv : FMap) (env : VMap) : Expr Op → M ValId
  | .lit l => do
    let v ← freshVal
    emit (.const v (YulSemantics.EVM.litValue l))
    pure v
  | .var x => liftO (env.get x)
  | .builtin op args => do
    let as ← trArgs fenv env args
    let d ← freshVal
    emit (.op [d] op as)
    pure d
  | .call fn args => do
    let as ← trArgs fenv env args
    let fid ← liftO (fenv.get fn)
    let d ← freshVal
    emit (.call [d] fid as)
    pure d

/-- Translate an argument list **right-to-left** (the Yul evaluation order:
the last argument's instructions are emitted first), returning the values in
source order. -/
def trArgs (fenv : FMap) (env : VMap) : List (Expr Op) → M (List ValId)
  | [] => pure []
  | e :: rest => do
    let restIds ← trArgs fenv env rest
    let i ← trExpr fenv env e
    pure (i :: restIds)

end

/-- Translate a statement-level expression producing `n` values (the
`let`/`assign` right-hand side; `n` may exceed 1 only for user calls). -/
def trExprN (fenv : FMap) (env : VMap) (n : Nat) : Expr Op → M (List ValId)
  | .call fn args => do
    let as ← trArgs fenv env args
    let fid ← liftO (fenv.get fn)
    let ds ← (List.range n).mapM (fun _ => freshVal)
    emit (.call ds fid as)
    pure ds
  | e => do
    if n = 1 then
      let v ← trExpr fenv env e
      pure [v]
    else reject

mutual

/-- Translate a function definition into its own `Func` (fresh per-function
state; the enclosing state is saved and restored). -/
def trFunc (fenv : FMap) (ps rs : List Ident) (body : List (Stmt Op)) :
    M Func := do
  let saved ← getFn
  setFn {}
  let entry ← newBlock []
  moveTo entry
  let pids ← ps.mapM (fun _ => freshVal)
  let rids ← rs.mapM fun _ => do
    let v ← freshVal
    emit (.const v 0)
    pure v
  -- no shadowing among params/rets (validator enforces distinctness)
  if !(ps ++ rs).Nodup then reject
  let env0 : VMap := ps.zip pids ++ rs.zip rids
  let renv ← trScope fenv env0 none (some rs) body
  if let some envEnd := renv then
    let vals ← edgeArgs envEnd rs
    sealCur (.ret vals)
  let done ← getFn
  setFn saved
  pure { params := pids, nrets := rs.length, entry := entry,
         blocks := done.blocks }
termination_by (sizeOf body, 2)

/-- Translate a statement list as a **scope**: allocate its hoisted function
slots, translate, and drop its declarations on exit (the `restore` of the
block rule). Returns the post-scope environment, or `none` if control was
diverted (terminator emitted on every path out). -/
def trScope (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (body : List (Stmt Op)) : M (Option VMap) := do
  let scope ← allocScope body
  let renv ← trStmts (scope :: fenv) env lctx rets false body
  match renv with
  | some env' => pure (some (env'.drop (env'.length - env.length)))
  | none => pure none
termination_by (sizeOf body, 1)

/-- Translate a statement list. `diverted = true` means an unconditional
terminator was already emitted: remaining statements are dead code and only
their `funDef`s (hoisted, hence callable earlier) are still translated. -/
def trStmts (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (diverted : Bool) :
    List (Stmt Op) → M (Option VMap)
  | [] => pure (if diverted then none else some env)
  | .funDef n ps rs fbody :: rest => do
    let fid ← liftO (fenv.get n)
    let f ← trFunc fenv ps rs fbody
    fillFunc fid f
    trStmts fenv env lctx rets diverted rest
  | s :: rest => do
    if diverted then
      -- dead code: skip, but keep walking for funDefs
      trStmts fenv env lctx rets true rest
    else do
      let renv ← trStmt fenv env lctx rets s
      match renv with
      | some env' => trStmts fenv env' lctx rets false rest
      | none => trStmts fenv env lctx rets true rest
termination_by ss => (sizeOf ss, 0)

/-- Translate one (non-`funDef`) statement. Returns the updated environment,
or `none` if the statement diverts control (its block got a terminator). -/
def trStmt (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) : Stmt Op → M (Option VMap)
  | .block body => trScope fenv env lctx rets body
  | .funDef _ _ _ _ => reject -- handled in trStmts
  | .letDecl vars none => do
    if vars.any env.mem || !vars.Nodup then reject
    let ids ← vars.mapM fun _ => do
      let v ← freshVal
      emit (.const v 0)
      pure v
    pure (some (vars.zip ids ++ env))
  | .letDecl vars (some e) => do
    if vars.any env.mem || !vars.Nodup then reject
    let ids ← trExprN fenv env vars.length e
    pure (some (vars.zip ids ++ env))
  | .assign vars e => do
    if !(vars.all env.mem) then reject
    let ids ← trExprN fenv env vars.length e
    pure (some (env.setMany vars ids))
  | .cond c body => do
    let cv ← trExpr fenv env c
    let X := modifiedX env [body]
    let xvals ← edgeArgs env X
    let bodyId ← newBlock []
    let joinParams ← X.mapM (fun _ => freshVal)
    let joinId ← newBlock joinParams
    sealCur (.branch cv ⟨bodyId, []⟩ ⟨joinId, xvals⟩)
    moveTo bodyId
    let renv ← trScope fenv env lctx rets body
    if let some env' := renv then
      let xv' ← edgeArgs env' X
      sealCur (.jump ⟨joinId, xv'⟩)
    moveTo joinId
    pure (some (env.setMany X joinParams))
  | .switch c cases dflt => do
    let sv ← trExpr fenv env c
    let bodies := cases.map Prod.snd ++ (match dflt with
      | some b => [b] | none => [])
    let X := modifiedX env bodies
    let joinParams ← X.mapM (fun _ => freshVal)
    let joinId ← newBlock joinParams
    trCases fenv env lctx rets sv X joinId cases dflt
    moveTo joinId
    pure (some (env.setMany X joinParams))
  | .forLoop init c post body => do
    -- the init scope covers the whole loop (`hoist init`)
    let scope ← allocScope init
    let fenv' := scope :: fenv
    let rinit ← trStmts fenv' env lctx rets false init
    match rinit with
    | none => pure none
    | some envI => do
      let X := modifiedX envI [post, body]
      let xvals ← edgeArgs envI X
      let hParams ← X.mapM (fun _ => freshVal)
      let hId ← newBlock hParams
      let exitParams ← X.mapM (fun _ => freshVal)
      let exitId ← newBlock exitParams
      let postParams ← X.mapM (fun _ => freshVal)
      let postId ← newBlock postParams
      sealCur (.jump ⟨hId, xvals⟩)
      moveTo hId
      let envH := envI.setMany X hParams
      let cv ← trExpr fenv' envH c
      let bodyId ← newBlock []
      let hX ← edgeArgs envH X
      sealCur (.branch cv ⟨bodyId, []⟩ ⟨exitId, hX⟩)
      moveTo bodyId
      let lctx' : LoopCtx := ⟨exitId, postId, X⟩
      let renvB ← trScope fenv' envH (some lctx') rets body
      if let some envB := renvB then
        let xvB ← edgeArgs envB X
        sealCur (.jump ⟨postId, xvB⟩)
      moveTo postId
      let envP := envI.setMany X postParams
      -- break/continue are invalid in `post` (no loop context there)
      let renvP ← trScope fenv' envP none rets post
      if let some envP' := renvP then
        let xvP ← edgeArgs envP' X
        sealCur (.jump ⟨hId, xvP⟩)
      moveTo exitId
      let envX := envI.setMany X exitParams
      -- drop the init declarations (the loop rule's `restore`)
      pure (some (envX.drop (envX.length - env.length)))
  | .exprStmt e =>
    (match e with
     | .builtin op args => do
       let as ← trArgs fenv env args
       if isHaltingOp op then do
         sealCur (.halt op as)
         pure none
       else do
         emit (.op [] op as)
         pure (some env)
     | .call fn args => do
       let as ← trArgs fenv env args
       let fid ← liftO (fenv.get fn)
       emit (.call [] fid as)
       pure (some env)
     | _ => reject)
  | .«break» => do
    match lctx with
    | none => reject
    | some l => do
      let vals ← edgeArgs env l.vars
      sealCur (.jump ⟨l.brkTgt, vals⟩)
      pure none
  | .«continue» => do
    match lctx with
    | none => reject
    | some l => do
      let vals ← edgeArgs env l.vars
      sealCur (.jump ⟨l.contTgt, vals⟩)
      pure none
  | .leave => do
    match rets with
    | none => reject
    | some rs => do
      let vals ← edgeArgs env rs
      sealCur (.ret vals)
      pure none
termination_by s => (sizeOf s, 0)

/-- Translate the switch case chain: each case gets an `eq` test block
(first test inline in the current block) and a body block jumping to the
join; the fall-through end runs the default (or jumps straight to the
join). -/
def trCases (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (sv : ValId) (X : List Ident)
    (joinId : BlockId) :
    List (Literal × List (Stmt Op)) → Option (List (Stmt Op)) → M Unit
  | [], none => do
    -- no default: fall through to the join with unchanged values
    let xvals ← edgeArgs env X
    sealCur (.jump ⟨joinId, xvals⟩)
  | [], some dbody => do
    let renv ← trScope fenv env lctx rets dbody
    match renv with
    | some env' => do
      let xv ← edgeArgs env' X
      sealCur (.jump ⟨joinId, xv⟩)
    | none => pure ()
  | (lit, cbody) :: restCases, dflt => do
    let t ← freshVal
    emit (.const t (YulSemantics.EVM.litValue lit))
    let e ← freshVal
    emit (.op [e] .eq [sv, t])
    let caseId ← newBlock []
    let nextId ← newBlock []
    sealCur (.branch e ⟨caseId, []⟩ ⟨nextId, []⟩)
    moveTo caseId
    let renv ← trScope fenv env lctx rets cbody
    if let some env' := renv then
      let xv ← edgeArgs env' X
      sealCur (.jump ⟨joinId, xv⟩)
    moveTo nextId
    trCases fenv env lctx rets sv X joinId restCases dflt
termination_by cs d => (sizeOf cs + sizeOf d, 0)

end

/-- Build the whole program from a top-level Yul block: `main` is translated
like a function with no parameters and no returns (`ret []` is the `.normal`
fall-through), user functions fill the slots allocated at their scopes. The
result is checked (`Prog.wfCheck`) — following the repo's checked-not-proved
well-formedness discipline — and rejected on failure. -/
def ofBlockRaw (prog : List (Stmt Op)) : Option Prog := do
  let build : M Func := do
    let entry ← newBlock []
    moveTo entry
    let renv ← trScope [] [] none none prog
    if let some _ := renv then
      sealCur (.ret [])
    let done ← getFn
    pure { params := [], nrets := 0, entry := entry, blocks := done.blocks }
  let (main, s) ← build {}
  let funcs ← s.funcs.mapM id
  some ⟨main, funcs⟩

/-- `ofBlockRaw` behind the well-formedness gate (the public entry point). -/
def ofBlock (prog : List (Stmt Op)) : Option Prog :=
  (ofBlockRaw prog).bind fun P => if P.wfCheck then some P else none

/-- The successful construction's output is well-formed: `ofBlock` returns
only programs that pass `Prog.wfCheck`. -/
theorem ofBlock_wfCheck {prog : List (Stmt Op)} {P : Prog}
    (hof : ofBlock prog = some P) : P.wfCheck = true := by
  unfold ofBlock at hof
  rcases hraw : ofBlockRaw prog with _ | Q <;> rw [hraw] at hof
  · exact absurd hof (by simp)
  · rw [show (some Q).bind (fun P => if P.wfCheck then some P else none)
        = if Q.wfCheck then some Q else none from rfl] at hof
    by_cases hwf : Q.wfCheck
    · rw [if_pos hwf] at hof
      obtain rfl := Option.some.inj hof
      exact hwf
    · rw [if_neg hwf] at hof
      exact absurd hof (by simp)

end YulEvmCompiler.SsaCfg
