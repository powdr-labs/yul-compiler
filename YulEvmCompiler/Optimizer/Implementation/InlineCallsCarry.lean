import YulEvmCompiler.Optimizer.Implementation.InlineCalls
import YulEvmCompiler.Optimizer.Implementation.ObjectPass
set_option warningAsError false
/-!
# InlineCallsCarry — call-carrying statement inliner (PROTOTYPE, unproven)

`InlineCalls` requires callee bodies to be *call-free* (`scopedExpr` rejects
any user call), so the leaf-first collapse stalls the moment one function in a
chain legitimately survives (a big math body over the `liveMax` bound, or a
multi-return decoder): every ancestor wrapper in the call chain is then pinned
out of line, paying full call protocol at each level. Diagnosed on
`FullMath.sol`: `fun_mulDiv` is a four-statement forwarding wrapper
(`r := 0; let t := impl(a,b,c); r := t; leave`) kept out of line only because
its body *contains a call*.

This pass inlines small call-**bearing** bodies and simply carries their inner
calls to the transplant site (solc FullInliner semantics). Function references
stay valid: Yul functions are visible throughout their defining block chain,
and the callee is a sibling of (or in an enclosing scope of) every call site
the pass rewrites.

Duplication and pressure gates: body ≤ `carryMaxStmts` statements, at most
`carryMaxCalls` carried calls, no self-recursion, and the shared `liveMax`
stack bound. Bodies the plain (call-free) classifier already accepts are left
to `InlineCalls`.

## Carried-call function-environment agreement (the soundness side condition)

A transplanted call-bearing body executes its inner (carried) calls under the
*caller's* function environment at the transplant site, whereas the original
runs them under the callee's defining scope. These agree unless an intervening
block between the callee's definition and the rewrite site *shadows* a carried
call name. The `Δ` threading enforces no such shadow can occur: `carrySurvives`
prunes a tracked entry `(f, d)` the moment a block (or a `for` init) redefines
`f` *or any name `d.ss` carries a call to*. Combined with `DeltaCompat` (every
tracked name resolves at the site to its recorded declaration), this makes the
invariant "every carried name resolves at the site exactly as at the callee's
definition" inductive. The carried body is then transported from the defining
scope to the site by `Step.funs_congr` (`FunCongr.lean`) — the semantic
function-environment congruence — with a prefix-agreement step for the extra
scopes the site sits under. solc IR has globally unique function names, so this
side condition prunes nothing on real input.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Carry-scoped well-formedness: `scopedStmt` minus the call-free rule -/

/-- Like `scopedExpr` without `!exprHasCall`: every variable read must be
bound, calls are allowed (their arguments are checked recursively via
`exprVars`). -/
def carryExpr (bound : List Ident) (e : Expr Op) : Bool :=
  (exprVars e).all bound.contains

mutual

def carryStmt (bound : List Ident) : Stmt Op → Option (List Ident)
  | .letDecl xs none => some (xs ++ bound)
  | .letDecl xs (some e) =>
      if carryExpr bound e then some (xs ++ bound) else none
  | .assign xs e =>
      if xs.all bound.contains && carryExpr bound e then some bound else none
  | .exprStmt e => if carryExpr bound e then some bound else none
  | .block body => if carryStmts bound body then some bound else none
  | .cond c body =>
      if carryExpr bound c && carryStmts bound body then some bound else none
  | .switch c cases dflt =>
      if carryExpr bound c && carryCases bound cases && carryDflt bound dflt
      then some bound else none
  | .funDef _ _ _ _ => none
  | .forLoop _ _ _ _ => none
  | .break => none
  | .continue => none
  | .leave => none

def carryStmts (bound : List Ident) : List (Stmt Op) → Bool
  | [] => true
  | s :: rest =>
      match carryStmt bound s with
      | some bound' => carryStmts bound' rest
      | none => false

def carryCases (bound : List Ident) : List (Literal × Block Op) → Bool
  | [] => true
  | (_, b) :: rest => carryStmts bound b && carryCases bound rest

def carryDflt (bound : List Ident) : Option (Block Op) → Bool
  | none => true
  | some b => carryStmts bound b

end

/-! ### Duplication gates -/

mutual

/-- User calls contained in an expression. -/
def exprCallNames : Expr Op → List Ident
  | .lit _ => []
  | .var _ => []
  | .builtin _ as => argsCallNames as
  | .call f as => f :: argsCallNames as

/-- User calls contained in an argument list. -/
def argsCallNames : List (Expr Op) → List Ident
  | [] => []
  | e :: rest => exprCallNames e ++ argsCallNames rest

end

mutual

/-- User calls contained in a statement. -/
def stmtCallNames : Stmt Op → List Ident
  | .letDecl _ none => []
  | .letDecl _ (some e) => exprCallNames e
  | .assign _ e => exprCallNames e
  | .exprStmt e => exprCallNames e
  | .block b => stmtsCallNames b
  | .cond c b => exprCallNames c ++ stmtsCallNames b
  | .switch c cs d => exprCallNames c ++ casesCallNames cs ++ dfltCallNames d
  | .funDef _ _ _ _ => []
  | .forLoop i c p b =>
      stmtsCallNames i ++ exprCallNames c ++ stmtsCallNames p ++ stmtsCallNames b
  | .break => []
  | .continue => []
  | .leave => []

/-- User calls contained in a statement list (function bodies excluded: a
carry-classified body contains no `funDef`). -/
def stmtsCallNames : List (Stmt Op) → List Ident
  | [] => []
  | s :: rest => stmtCallNames s ++ stmtsCallNames rest

/-- User calls contained in `switch` case bodies. -/
def casesCallNames : List (Literal × Block Op) → List Ident
  | [] => []
  | (_, b) :: rest => stmtsCallNames b ++ casesCallNames rest

/-- User calls contained in a `switch` default. -/
def dfltCallNames : Option (Block Op) → List Ident
  | none => []
  | some b => stmtsCallNames b

end

/-- Statement budget for a carried body. -/
def carryMaxStmts : Nat := 8

/-- Carried-call budget for a carried body. -/
def carryMaxCalls : Nat := 2

/-- Classify a call-bearing declaration as carry-inlinable. Bodies the plain
classifier accepts are `InlineCalls`' business; self-recursive bodies would
re-expand every round. -/
def carryClassifyDecl (f : Ident) (ps rs : List Ident) (body : Block Op) :
    Option IDecl :=
  if (classifyDecl ps rs body).isSome then none
  else if (ps ++ rs).Nodup && carryStmts (ps ++ rs) (dropTrailingLeave body) then
    let d : IDecl := ⟨ps, rs, dropTrailingLeave body⟩
    let calls := stmtsCallNames d.ss
    if calls.length ≤ carryMaxCalls && !calls.contains f then some d else none
  else none

/-- Profitability + pressure gate for carried bodies. -/
def carryOK (d : IDecl) : Bool :=
  d.rs.length ≤ 2 &&
  d.ss.length ≤ carryMaxStmts &&
  liveMaxStmts (d.ps.length + d.rs.length) d.ss ≤ 13

/-- `hoistDecls` with the carry classifier. -/
def carryHoistDecls (seen : List Ident) : List (Stmt Op) → DEnv
  | [] => []
  | .funDef f ps rs body :: rest =>
      if seen.contains f then carryHoistDecls seen rest
      else
        match carryClassifyDecl f ps rs body with
        | some d => (f, d) :: carryHoistDecls (f :: seen) rest
        | none => carryHoistDecls (f :: seen) rest
  | _ :: rest => carryHoistDecls seen rest

/-- A carry entry `(f, d)` **survives** entry into a block whose function
definitions are `defs` only when that block redefines neither `f` nor any name
`d.ss` carries a call to. Redefining a carried name would make the transplanted
copy's inner call resolve to the shadowing definition rather than the one live
at `f`'s definition — the no-shadowing side condition that keeps the carried
calls' function-environment agreement inductive (solc IR has globally unique
function names, so this prunes nothing there). -/
def carrySurvives (defs : List Ident) (p : Ident × IDecl) : Bool :=
  !defs.contains p.1 && (stmtsCallNames p.2.ss).all (fun g => !defs.contains g)

/-- `deltaExtend` with the carry classifier and the carried-name shadow prune. -/
def carryDeltaExtend (Δ : DEnv) (body : List (Stmt Op)) : DEnv :=
  carryHoistDecls [] body ++ Δ.filter (carrySurvives (definedFuns body))

/-! ### The transform (mirrors `icStmt`; `inlineCore` and `siteOK` reused) -/

mutual

def cyStmt (Δ : DEnv) : Stmt Op → List (Stmt Op)
  | .letDecl xs (some (.call f as)) =>
      match lookupDelta Δ f with
      | some d =>
          if carryOK d && siteOK d xs as true then
            [.letDecl xs none, inlineCore d xs as]
          else
            [.letDecl xs (some (.call f as))]
      | none => [.letDecl xs (some (.call f as))]
  | .assign xs (.call f as) =>
      match lookupDelta Δ f with
      | some d =>
          if carryOK d && siteOK d xs as false then
            [inlineCore d xs as]
          else
            [.assign xs (.call f as)]
      | none => [.assign xs (.call f as)]
  | .exprStmt (.call f as) =>
      match lookupDelta Δ f with
      | some d =>
          if carryOK d && siteOK d [] as false then
            [inlineCore d [] as]
          else
            [.exprStmt (.call f as)]
      | none => [.exprStmt (.call f as)]
  | .block body => [.block (cyBlock Δ body)]
  | .funDef n ps rs body => [.funDef n ps rs (cyBlock Δ body)]
  | .cond c body => [.cond c (cyBlock Δ body)]
  | .switch c cases dflt => [.switch c (cyCases Δ cases) (cyDflt Δ dflt)]
  | .forLoop init c post body =>
      let ΔL := Δ.filter (carrySurvives (definedFuns init))
      [.forLoop init c (cyBlock ΔL post) (cyBlock ΔL body)]
  | s => [s]

def cyStmts (Δ : DEnv) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => cyStmt Δ s ++ cyStmts Δ rest

def cyBlock (Δ : DEnv) (body : List (Stmt Op)) : List (Stmt Op) :=
  cyStmts (carryDeltaExtend Δ body) body

def cyCases (Δ : DEnv) : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, cyBlock Δ b) :: cyCases Δ rest

def cyDflt (Δ : DEnv) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (cyBlock Δ b)

end

/-- Pass entry point. -/
def inlineCallsCarryBlock (b : Block Op) : Block Op := cyBlock [] b

-- The `inlineCallsCarry : LocalPass D` bundle and its `resolveInlineCallsCarryBlock_equiv`
-- resolution congruence live in `InlineCallsCarrySound2` (they require the
-- `cy_fwd`/`cy_bwd` simulation, which would form an import cycle here).

end YulEvmCompiler.Optimizer
