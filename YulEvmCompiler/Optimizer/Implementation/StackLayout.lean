import YulEvmCompiler.Optimizer.Implementation.Frame
import YulEvmCompiler.Optimizer.Implementation.FreshenCalls
import YulEvmCompiler.Optimizer.Implementation.DeadPure
import YulEvmCompiler.Compile
import YulSemantics.Dialect.EVM
set_option warningAsError true
/-!
# Smart stack layout

The executable half of the expression scheduler, liveness-guided slot reuse,
and dominance-guided tail-scope pass. Soundness lives in
`StackLayoutSound.lean`; keeping policy separate makes each layout choice
independently testable.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### Expression-pressure scheduling

Yul evaluates arguments right-to-left.  A left-associated addition tree such
as `add(add(add(a, b), c), d)` therefore keeps `d`, then `c`, live while it
descends toward `a`; on the EVM that can turn an otherwise shallow variable
access into a forbidden `DUP17`.  Reassociating the tree to
`add(a, add(b, add(c, d)))` preserves the exact leaf evaluation order
(`d, c, b, a`) while reducing the number of pending operands.

`rightAssocAdd` is the Sethi--Ullman-style local scheduler for this common
all-live case.  The surrounding traversal first schedules children, then
right-associates each addition spine. -/

def rightAssocAdd : Expr Op → Expr Op → Expr Op
  | .builtin .add [a, b], c => rightAssocAdd a (rightAssocAdd b c)
  | a, c => .builtin .add [a, c]
  termination_by a => sizeOf a
  decreasing_by all_goals simp_wf; omega

def scheduleBuiltin (op : Op) (args : List (Expr Op)) : Expr Op :=
  if op = .add then
    match args with
    | [a, b] => rightAssocAdd a b
    | _ => .builtin op args
  else
    .builtin op args

mutual
  def scheduleExpr : Expr Op → Expr Op
    | .lit l => .lit l
    | .var x => .var x
    | .builtin op args => scheduleBuiltin op (scheduleArgs args)
    | .call f args => .call f (scheduleArgs args)

  def scheduleArgs : List (Expr Op) → List (Expr Op)
    | [] => []
    | e :: rest => scheduleExpr e :: scheduleArgs rest
end

mutual
  def scheduleStmt : Stmt Op → Stmt Op
    | .block body => .block (scheduleStmts body)
    | .funDef f ps rs body => .funDef f ps rs (scheduleStmts body)
    | .letDecl xs val => .letDecl xs (val.map scheduleExpr)
    | .assign xs e => .assign xs (scheduleExpr e)
    | .cond c body => .cond (scheduleExpr c) (scheduleStmts body)
    | .switch c cases dflt =>
        .switch (scheduleExpr c) (scheduleCases cases)
          (match dflt with | none => none | some b => some (scheduleStmts b))
    | .forLoop init c post body =>
        .forLoop init (scheduleExpr c)
          (scheduleStmts post) (scheduleStmts body)
    | .exprStmt e => .exprStmt (scheduleExpr e)
    | .break => .break
    | .continue => .continue
    | .leave => .leave
    termination_by s => 2 * sizeOf s

  def scheduleStmts : List (Stmt Op) → List (Stmt Op)
    | [] => []
    | s :: rest => scheduleStmt s :: scheduleStmts rest
    termination_by ss => 2 * sizeOf ss + 1

  def scheduleCases : List (Literal × Block Op) → List (Literal × Block Op)
    | [] => []
    | (l, b) :: rest => (l, scheduleStmts b) :: scheduleCases rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

abbrev Rename := List (Ident × Ident)

def renameLookup (r : Rename) (x : Ident) : Ident :=
  match r.find? (fun p => p.1 = x) with
  | some p => p.2
  | none => x

mutual
  def renameExpr (r : Rename) : Expr Op → Expr Op
    | .lit l => .lit l
    | .var x => .var (renameLookup r x)
    | .builtin op args => .builtin op (renameArgs r args)
    | .call f args => .call f (renameArgs r args)

  def renameArgs (r : Rename) : List (Expr Op) → List (Expr Op)
    | [] => []
    | e :: es => renameExpr r e :: renameArgs r es
end

mutual
  /-- Mentions of `x` inside nested function bodies, which run in fresh
  variable environments and are intentionally not renamed with their caller. -/
  def stmtFunMentions (x : Ident) : Stmt Op → Bool
    | .block body => stmtsFunMention x body
    | s@(.funDef _ _ _ _) => stmtMentions x s
    | .cond _ body => stmtsFunMention x body
    | .switch _ cases dflt =>
        casesFunMention x cases || optBlockFunMentions x dflt
    | .forLoop init _ post body =>
        stmtsFunMention x init || stmtsFunMention x post || stmtsFunMention x body
    | _ => false

  def stmtsFunMention (x : Ident) : Block Op → Bool
    | [] => false
    | s :: rest => stmtFunMentions x s || stmtsFunMention x rest

  def casesFunMention (x : Ident) : List (Literal × Block Op) → Bool
    | [] => false
    | (_, body) :: rest => stmtsFunMention x body || casesFunMention x rest

  def optBlockFunMentions (x : Ident) : Option (Block Op) → Bool
    | none => false
    | some body => stmtsFunMention x body
end

mutual
  def renameStmt (r : Rename) : Stmt Op → Stmt Op
    | .block body => .block (renameStmts r body)
    | .funDef f ps rs body => .funDef f ps rs body
    | .letDecl xs val => .letDecl xs (val.map (renameExpr r))
    | .assign xs e => .assign (xs.map (renameLookup r)) (renameExpr r e)
    | .cond c body => .cond (renameExpr r c) (renameStmts r body)
    | .switch c cases dflt =>
        .switch (renameExpr r c) (renameCases r cases)
          (match dflt with | none => none | some b => some (renameStmts r b))
    | .forLoop init c post body =>
        .forLoop (renameStmts r init) (renameExpr r c)
          (renameStmts r post) (renameStmts r body)
    | .exprStmt e => .exprStmt (renameExpr r e)
    | .break => .break
    | .continue => .continue
    | .leave => .leave
    termination_by s => 2 * sizeOf s

  def renameStmts (r : Rename) : List (Stmt Op) → List (Stmt Op)
    | [] => []
    | s :: ss => renameStmt r s :: renameStmts r ss
    termination_by ss => 2 * sizeOf ss + 1

  def renameCases (r : Rename) : List (Literal × Block Op) → List (Literal × Block Op)
    | [] => []
    | (l, b) :: cs => (l, renameStmts r b) :: renameCases r cs
    termination_by cs => 2 * sizeOf cs + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  /-- Whether a statement introduces a caller-local binding named `x`.
  Function bodies have fresh variable environments and are therefore excluded. -/
  def stmtDeclares (x : Ident) : Stmt Op → Bool
    | .block body => stmtsDeclare x body
    | .funDef _ _ _ _ => false
    | .letDecl xs _ => xs.contains x
    | .assign _ _ => false
    | .cond _ body => stmtsDeclare x body
    | .switch _ cases dflt =>
        casesDeclare x cases || optBlockDeclares x dflt
    | .forLoop init _ post body =>
        stmtsDeclare x init || stmtsDeclare x post || stmtsDeclare x body
    | .exprStmt _ | .break | .continue | .leave => false

  def stmtsDeclare (x : Ident) : Block Op → Bool
    | [] => false
    | s :: rest => stmtDeclares x s || stmtsDeclare x rest

  def casesDeclare (x : Ident) : List (Literal × Block Op) → Bool
    | [] => false
    | (_, body) :: rest => stmtsDeclare x body || casesDeclare x rest

  def optBlockDeclares (x : Ident) : Option (Block Op) → Bool
    | none => false
    | some body => stmtsDeclare x body
end

def reusableSlot (layout owned : List Ident) (_y : Ident) (_e : Expr Op)
    (rest : Block Op) : Option Ident :=
  owned.find? fun x =>
      match layout.findIdx? (fun z => z = x) with
      | some idx => idx < 16 && x != _y && !layout.contains _y &&
          !stmtsMentions x rest && !stmtsDeclare _y rest &&
          !stmtsFunMention _y rest
      | none => false

/-! ### Tail-carrier scope sinking

At a block tail, an outer result write can become unreachable solely because
the block's locals are still live on the operand stack.  When the block starts
with a singleton local `carrier` and ends in `result := e; leave`, keep the
carrier in the outer block, move the intervening computation into a nested
block, write `e` to the carrier there, and copy it to `result` after the nested
scope has popped its locals.  The carrier declaration dominates the whole
region; the final copy is its only live-out use.

The policy fires only when the original result slot is at depth 16 or greater
and the scoped form makes it reachable.  Direct function definitions are
excluded because moving them would change the block's hoisted scope. -/

def splitAssignLeave : Block Op → Option (Block Op × Ident × Expr Op)
  | [.assign [r] e, .leave] => some ([], r, e)
  | s :: rest => do
      let (middle, r, e) ← splitAssignLeave rest
      pure (s :: middle, r, e)
  | _ => none

def directSlots : Block Op → Nat
  | [] => 0
  | .letDecl xs _ :: rest => xs.length + directSlots rest
  | _ :: rest => directSlots rest

def hasDirectFun : Block Op → Bool
  | [] => false
  | .funDef _ _ _ _ :: _ => true
  | _ :: rest => hasDirectFun rest

def carrierInit (carrier : Ident) : Option (Expr Op) → Block Op
  | none => []
  | some e => [.assign [carrier] e]

def carrierInitSafe (carrier : Ident) : Option (Expr Op) → Bool
  | none => true
  | some e => !exprMentions carrier e

def scopeTailHere (layout : List Ident) : Block Op → Option (Block Op)
  | .letDecl [carrier] val :: rest => do
      let (middle, result, e) ← splitAssignLeave rest
      let resultDepth ← layout.findIdx? (fun x => x = result)
      if resultDepth + 1 < 16 &&
          16 ≤ resultDepth + 1 + directSlots middle &&
          carrier != result && !layout.contains carrier &&
          carrierInitSafe carrier val &&
          !stmtsDeclare carrier middle && !stmtsDeclare result middle &&
          !hasDirectFun middle && !middle.isEmpty then
        some [.letDecl [carrier] none,
          .block (carrierInit carrier val ++ middle ++ [.assign [carrier] e]),
          .assign [result] (.var carrier), .leave]
      else none
  | _ => none

/-! Like slot coalescing, scope sinking exposes one proof-sized rewrite per
iteration.  Layout changes only at direct declarations; all structured
statements restore their entry layout. -/

mutual
  def scopeOneStmt (layout : List Ident) : Stmt Op → Option (Stmt Op)
    | .block body => (.block ·) <$> scopeOneStmts layout body
    | .funDef f ps rs body =>
        (.funDef f ps rs ·) <$> scopeOneStmts (ps ++ rs) body
    | .cond c body => (.cond c ·) <$> scopeOneStmts layout body
    | .switch c cases dflt =>
        match scopeOneCases layout cases with
        | some cases' => some (.switch c cases' dflt)
        | none =>
            match dflt with
            | some body =>
                (fun body' => .switch c cases (some body')) <$>
                  scopeOneStmts layout body
            | none => none
    | .forLoop init c post body =>
        match scopeOneStmts layout post with
        | some post' => some (.forLoop init c post' body)
        | none => (.forLoop init c post ·) <$> scopeOneStmts layout body
    | _ => none
    termination_by s => 2 * sizeOf s

  def scopeOneStmts (layout : List Ident) (ss : Block Op) : Option (Block Op) :=
    match scopeTailHere layout ss with
    | some ss' => some ss'
    | none =>
        match ss with
        | [] => none
        | s :: rest =>
            match scopeOneStmt layout s with
            | some s' => some (s' :: rest)
            | none =>
                let layout' := match s with
                  | .letDecl xs _ => xs ++ layout
                  | _ => layout
                (s :: ·) <$> scopeOneStmts layout' rest
    termination_by 2 * sizeOf ss + 1

  def scopeOneCases (layout : List Ident) :
      List (Literal × Block Op) → Option (List (Literal × Block Op))
    | [] => none
    | (l, body) :: rest =>
        match scopeOneStmts layout body with
        | some body' => some ((l, body') :: rest)
        | none => ((l, body) :: ·) <$> scopeOneCases layout rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def iterateTailScopeFrom : Nat → List Ident → Block Op → Block Op
  | 0, _, b => b
  | n + 1, layout, b =>
      match scopeOneStmts layout b with
      | some b' => iterateTailScopeFrom n layout b'
      | none => b

def iterateTailScope (n : Nat) (b : Block Op) : Block Op :=
  iterateTailScopeFrom n [] b

/-! ### Adjacent call-result copy-back

Solc commonly emits `let t₁…tₙ := f(as)` followed immediately by singleton
copies `dᵢ := tᵢ`.  When the temporaries are absent from the suffix, retargeting
the call to `d₁…dₙ` removes all `tᵢ` slots.  This is a dominance/liveness
rewrite: the call definition dominates every copy, and the adjacent copies are
the complete live range of the temporary results.

The exact adjacent shape is intentional.  Mention-freedom alone would not
permit moving destination writes across intervening effects. -/

def takeCopyBack : List Ident → Block Op → Option (List Ident × Block Op)
  | [], rest => some ([], rest)
  | t :: ts, .assign [d] (.var u) :: rest => do
      if u != t then none else
      let (ds, suffix) ← takeCopyBack ts rest
      some (d :: ds, suffix)
  | _, _ => none

def copyBackStmts (ts ds : List Ident) : Block Op :=
  (ds.zip ts).map fun p => .assign [p.1] (.var p.2)

def copyBackHere (layout : List Ident) : Block Op → Option (Block Op)
  | .letDecl ts (some call@(.call _ _)) :: rest => do
      if ts.isEmpty || !ts.Nodup then none else
      let (ds, suffix) ← takeCopyBack ts rest
      if ds.Nodup && ds.all layout.contains &&
          ts.all (fun t => !ds.contains t && !stmtsMentions t suffix) then
        some (.assign ds call :: suffix)
      else none
  | _ => none

/-- Direct declarations extend the backend layout; structured statements
restore their entry layout. -/
def layoutAfter : List Ident → Block Op → List Ident
  | layout, [] => layout
  | layout, .letDecl xs _ :: rest => layoutAfter (xs ++ layout) rest
  | layout, _ :: rest => layoutAfter layout rest

mutual
  def copyOneStmt (layout : List Ident) : Stmt Op → Option (Stmt Op)
    | .block body => (.block ·) <$> copyOneStmts layout body
    | .funDef f ps rs body =>
        (.funDef f ps rs ·) <$> copyOneStmts (ps ++ rs) body
    | .cond c body => (.cond c ·) <$> copyOneStmts layout body
    | .switch c cases dflt =>
        match copyOneCases layout cases with
        | some cases' => some (.switch c cases' dflt)
        | none =>
            match dflt with
            | some body =>
                (fun body' => .switch c cases (some body')) <$>
                  copyOneStmts layout body
            | none => none
    | .forLoop init c post body =>
        let loopLayout := layoutAfter layout init
        match copyOneStmts loopLayout post with
        | some post' => some (.forLoop init c post' body)
        | none => (.forLoop init c post ·) <$> copyOneStmts loopLayout body
    | _ => none
    termination_by s => 2 * sizeOf s

  def copyOneStmts (layout : List Ident) (ss : Block Op) : Option (Block Op) :=
    match copyBackHere layout ss with
    | some ss' => some ss'
    | none =>
        match ss with
        | [] => none
        | s :: rest =>
            match copyOneStmt layout s with
            | some s' => some (s' :: rest)
            | none =>
                let layout' := match s with
                  | .letDecl xs _ => xs ++ layout
                  | _ => layout
                (s :: ·) <$> copyOneStmts layout' rest
    termination_by 2 * sizeOf ss + 1

  def copyOneCases (layout : List Ident) :
      List (Literal × Block Op) → Option (List (Literal × Block Op))
    | [] => none
    | (l, body) :: rest =>
        match copyOneStmts layout body with
        | some body' => some ((l, body') :: rest)
        | none => ((l, body) :: ·) <$> copyOneCases layout rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def iterateCopyBackFrom : Nat → List Ident → Block Op → Block Op
  | 0, _, b => b
  | n + 1, layout, b =>
      match copyOneStmts layout b with
      | some b' => iterateCopyBackFrom n layout b'
      | none => b

def iterateCopyBack (n : Nat) (b : Block Op) : Block Op :=
  iterateCopyBackFrom n [] b

/-! ### Pressure-triggered right-to-left call-argument staging

When pending arguments and return slots push an earlier argument below
`DUP16`, evaluate every argument into a fresh local in Yul's native
right-to-left order, then make the call from the adjacent carrier frame.  The
fresh block is the nearest common dominator of the call and all carrier uses;
its exit is their common post-dominator, so no carrier remains live afterward.
-/

mutual
  def exprFits (Phi : FMap) (layout : List Ident) (off : Nat) : Expr Op → Bool
    | .lit _ => true
    | .var x =>
        match layout.findIdx? (fun y => y = x) with
        | some idx => off + idx < 16
        | none => false
    | .builtin _ args => argsFit Phi layout off args
    | .call f args =>
        match lookupF Phi f with
        | some (info, _) => argsFit Phi layout (off + 1 + info.rets) args
        | none => false

  def argsFit (Phi : FMap) (layout : List Ident) (off : Nat) :
      List (Expr Op) → Bool
    | [] => true
    | e :: rest => argsFit Phi layout off rest &&
        exprFits Phi layout (off + rest.length) e
end

def assignsFit (layout xs : List Ident) : Bool :=
  xs.zipIdx.all fun (x, i) =>
    match layout.findIdx? (fun y => y = x) with
    | some idx => idx + (xs.length - i - 1) < 16
    | none => false

def callCarriers (P : String) (n : Nat) : List Ident :=
  (List.range n).map fun i => s!"{P}a{i}"

def stageDecls (names : List Ident) (args : List (Expr Op)) : Block Op :=
  (names.zip args).reverse.map fun p => .letDecl [p.1] (some p.2)

def stageCore (P : String) (xs : List Ident) (f : Ident)
    (args : List (Expr Op)) : Stmt Op :=
  let names := callCarriers P args.length
  .block (stageDecls names args ++
    [.assign xs (.call f (names.map Expr.var))])

def stagedArgsFit (Phi : FMap) :
    List Ident → List Ident → List (Expr Op) → Bool
  | _, [], [] => true
  | layout, _ :: names, e :: args =>
      stagedArgsFit Phi layout names args &&
        exprFits Phi (names.reverse ++ layout) 0 e
  | _, _, _ => false

def stageWanted (Phi : FMap) (layout : List Ident) (xs : List Ident)
    (f : Ident) (args : List (Expr Op)) (names : List Ident) : Bool :=
  !args.isEmpty && !exprFits Phi layout 0 (.call f args) &&
    stagedArgsFit Phi layout names args &&
    exprFits Phi (names ++ layout) 0 (.call f (names.map Expr.var)) &&
    assignsFit (names ++ layout) xs && argsHaveCall args == false &&
    argsShadowOK [] (names.zip args) && names.Nodup &&
    xs.all (fun x => !names.contains x)

mutual
  def stageOneStmt (P : String) (Phi : FMap) (layout : List Ident) :
      Stmt Op → Option (Stmt Op)
    | .assign xs (.call f args) =>
        let names := callCarriers P args.length
        if stageWanted Phi layout xs f args names then
          some (stageCore P xs f args)
        else none
    | .block body => (.block ·) <$> stageOneStmts P Phi layout body
    | .funDef f ps rs body =>
        (.funDef f ps rs ·) <$> stageOneStmts P Phi (ps ++ rs) body
    | .cond c body => (.cond c ·) <$> stageOneStmts P Phi layout body
    | .switch c cases dflt =>
        match stageOneCases P Phi layout cases with
        | some cases' => some (.switch c cases' dflt)
        | none =>
            match dflt with
            | some body =>
                (fun body' => .switch c cases (some body')) <$>
                  stageOneStmts P Phi layout body
            | none => none
    | .forLoop init c post body =>
        let (scope, _) := hoistInfos 0 init
        let Phi' := scope :: Phi
        let loopLayout := layoutAfter layout init
        match stageOneStmts P Phi' loopLayout post with
        | some post' => some (.forLoop init c post' body)
        | none => (.forLoop init c post ·) <$>
            stageOneStmts P Phi' loopLayout body
    | _ => none
    termination_by s => 2 * sizeOf s

  def stageOneStmts (P : String) (Phi : FMap) (layout : List Ident)
      (ss : Block Op) : Option (Block Op) :=
    match ss with
    | [] => none
    | s :: rest =>
        match stageOneStmt P Phi layout s with
        | some s' => some (s' :: rest)
        | none =>
            let layout' := match s with
              | .letDecl xs _ => xs ++ layout
              | _ => layout
            (s :: ·) <$> stageOneStmts P Phi layout' rest
    termination_by 2 * sizeOf ss + 1

  def stageOneCases (P : String) (Phi : FMap) (layout : List Ident) :
      List (Literal × Block Op) → Option (List (Literal × Block Op))
    | [] => none
    | (l, body) :: rest =>
        match stageOneStmts P Phi layout body with
        | some body' => some ((l, body') :: rest)
        | none => ((l, body) :: ·) <$> stageOneCases P Phi layout rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def iterateStageWithLayout : Nat → String → FMap → List Ident →
    Block Op → Block Op
  | 0, _, _, _, b => b
  | n + 1, P, Phi, layout, b =>
      match stageOneStmts P Phi layout b with
      | some b' => iterateStageWithLayout n P Phi layout b'
      | none => b

def iterateStageWith (n : Nat) (P : String) (Phi : FMap)
    (b : Block Op) : Block Op :=
  iterateStageWithLayout n P Phi [] b

def iterateStageCalls (fuel : Nat) (P : String) (b : Block Op) : Block Op :=
  let (scope, _) := hoistInfos 0 b
  iterateStageWith fuel P [scope] b

def stageCallsBlock (b : Block Op) : Block Op :=
  match freshPrefix (stmtsIdents b) with
  | some P => iterateStageCalls 16384 P b
  | none => b

/-! ### Function-result live-range splitting

A function result is fixed at the bottom of its frame, so a long body can make
later updates unreachable even when all branch-local values are well laid out.
Split such a result at the function-entry dominator: the body uses a fresh
shallow shadow, every `leave` copies it back, and normal fallthrough copies it
back after an inner block has discarded all body locals. -/

mutual
  def deepAssignStmt (x : Ident) (layout : List Ident) : Stmt Op → Bool
    | .block body | .cond _ body => deepAssignStmts x layout body
    | .funDef _ _ _ _ => false
    | .letDecl _ _ | .exprStmt _ | .break | .continue | .leave => false
    | .assign xs _ => xs.contains x && !assignsFit layout xs
    | .switch _ cases dflt =>
        deepAssignCases x layout cases || deepAssignDflt x layout dflt
    | .forLoop init _ post body =>
        let loopLayout := layoutAfter layout init
        deepAssignStmts x layout init || deepAssignStmts x loopLayout post ||
          deepAssignStmts x loopLayout body
    termination_by s => 2 * sizeOf s

  def deepAssignStmts (x : Ident) (layout : List Ident) : Block Op → Bool
    | [] => false
    | s :: rest =>
        let layout' := match s with
          | .letDecl xs _ => xs ++ layout
          | _ => layout
        deepAssignStmt x layout s || deepAssignStmts x layout' rest
    termination_by ss => 2 * sizeOf ss + 1

  def deepAssignCases (x : Ident) (layout : List Ident) :
      List (Literal × Block Op) → Bool
    | [] => false
    | (_, body) :: rest =>
        deepAssignStmts x layout body || deepAssignCases x layout rest
    termination_by cases => 2 * sizeOf cases + 1

  def deepAssignDflt (x : Ident) (layout : List Ident) :
      Option (Block Op) → Bool
    | none => false
    | some body => deepAssignStmts x layout body
    termination_by dflt => 2 * sizeOf dflt + 1
  decreasing_by
    all_goals simp_wf
end

mutual
  def copyResultOnLeaveStmt (result shadow : Ident) :
      Stmt Op → Block Op
    | .block body => [.block (copyResultOnLeaveStmts result shadow body)]
    | s@(.funDef _ _ _ _) => [s]
    | .letDecl xs val => [.letDecl xs val]
    | .assign xs e => [.assign xs e]
    | .cond c body => [.cond c (copyResultOnLeaveStmts result shadow body)]
    | .switch c cases dflt => [.switch c
        (copyResultOnLeaveCases result shadow cases)
        (copyResultOnLeaveDflt result shadow dflt)]
    | .forLoop init c post body => [.forLoop
        (copyResultOnLeaveStmts result shadow init) c
        (copyResultOnLeaveStmts result shadow post)
        (copyResultOnLeaveStmts result shadow body)]
    | .exprStmt e => [.exprStmt e]
    | .break => [.break]
    | .continue => [.continue]
    | .leave => [.assign [result] (.var shadow), .leave]
    termination_by s => 2 * sizeOf s

  def copyResultOnLeaveStmts (result shadow : Ident) :
      Block Op → Block Op
    | [] => []
    | s :: rest => copyResultOnLeaveStmt result shadow s ++
        copyResultOnLeaveStmts result shadow rest
    termination_by ss => 2 * sizeOf ss + 1

  def copyResultOnLeaveCases (result shadow : Ident) :
      List (Literal × Block Op) → List (Literal × Block Op)
    | [] => []
    | (lit, body) :: rest =>
        (lit, copyResultOnLeaveStmts result shadow body) ::
          copyResultOnLeaveCases result shadow rest
    termination_by cases => 2 * sizeOf cases + 1

  def copyResultOnLeaveDflt (result shadow : Ident) :
      Option (Block Op) → Option (Block Op)
    | none => none
    | some body => some (copyResultOnLeaveStmts result shadow body)
    termination_by dflt => 2 * sizeOf dflt + 1
  decreasing_by
    all_goals simp_wf
end

def splitDeepResult (P : String) : Stmt Op → Option (Stmt Op)
  | .funDef f ps rs body => do
      let result ← rs.find? (fun x => deepAssignStmts x (ps ++ rs) body)
      let shadow := P ++ "result"
      let layout := ps ++ rs
      if !layout.contains shadow &&
          (layout.findIdx? (fun y => y = result)).any (fun i => i < 15) then
        let renamed := renameStmts [(result, shadow)] body
        let ranged := copyResultOnLeaveStmts result shadow renamed
        some (.funDef f ps rs
          [.letDecl [shadow] (some (.var result)), .block ranged,
           .assign [result] (.var shadow)])
      else none
  | _ => none

def splitOneDeepResult (P : String) : Block Op → Option (Block Op)
  | [] => none
  | s :: rest =>
      match splitDeepResult P s with
      | some s' => some (s' :: rest)
      | none => (s :: ·) <$> splitOneDeepResult P rest

def iterateDeepResults : Nat → Block Op → Block Op
  | 0, body => body
  | n + 1, body =>
      match freshPrefix (stmtsIdents body) with
      | none => body
      | some P =>
          match splitOneDeepResult P body with
          | some body' => iterateDeepResults n body'
          | none => body

/-! ### Shallow available-copy forwarding

When an existing shallow local receives the current value of a deeper binding,
subsequent reads can use that local until either side is written or shadowed.
This is ordinary forward available-copy dataflow, oriented toward the EVM's
sixteen-slot access window. It introduces neither evaluations nor stack slots. -/

mutual
  def useAliasExpr (source copy : Ident) : Expr Op → Expr Op
    | .lit l => .lit l
    | .var x => .var (if x = source then copy else x)
    | .builtin op args => .builtin op (useAliasArgs source copy args)
    | .call f args => .call f (useAliasArgs source copy args)

  def useAliasArgs (source copy : Ident) : List (Expr Op) → List (Expr Op)
    | [] => []
    | e :: rest => useAliasExpr source copy e :: useAliasArgs source copy rest
end

def aliasSelfAssign (copy : Ident) : Stmt Op → Bool
  | .assign [x] (.var y) => x = copy && y = copy
  | _ => false

/-! `Propagate` deliberately gates copy tracking in large nested regions.  At
an alias site the equality is already established, so stack layout uses the
same proved transfer functions but keeps tracking enabled throughout the
region.  The corresponding `PropRel` certificate is in `StackLayoutSound`. -/

mutual
  def aliasPropStmt (sigma : PEnv) : Stmt Op → Stmt Op × PEnv
    | .block body =>
        (.block (aliasPropStmts sigma body).1, prune sigma (writeSetStmts body))
    | .funDef n ps rs body =>
        (.funDef n ps rs (aliasPropStmts [] body).1, sigma)
    | .letDecl xs none => (.letDecl xs none, letZeroEnv sigma xs)
    | .letDecl xs (some e) =>
        let rhs := rhsExpr sigma e
        (.letDecl xs (some rhs), letEnv true sigma xs rhs)
    | .assign xs e =>
        let rhs := rhsExpr sigma e
        (.assign xs rhs, assignEnv true sigma xs rhs)
    | .cond c body =>
        (.cond (substExpr sigma c) (aliasPropStmts sigma body).1,
          prune sigma (writeSetStmts body))
    | .switch c cases dflt =>
        (.switch (substExpr sigma c) (aliasPropCases sigma cases)
          (aliasPropDflt sigma dflt),
          prune sigma (writeSetCases cases ++ writeSetDflt dflt))
    | .forLoop init c post body =>
        let pinit := aliasPropStmts sigma init
        let sigmaL := prune pinit.2 (writeSetStmts post ++ writeSetStmts body)
        (.forLoop pinit.1 (substExpr sigmaL c)
          (aliasPropStmts sigmaL post).1 (aliasPropStmts sigmaL body).1,
          prune sigma
            (writeSetStmts init ++ writeSetStmts post ++ writeSetStmts body))
    | .exprStmt e => (.exprStmt (substExpr sigma e), sigma)
    | .break => (.break, sigma)
    | .continue => (.continue, sigma)
    | .leave => (.leave, sigma)
    termination_by s => 2 * sizeOf s

  def aliasPropStmts (sigma : PEnv) : Block Op → Block Op × PEnv
    | [] => ([], sigma)
    | s :: rest =>
        let ps := aliasPropStmt sigma s
        let prest := aliasPropStmts ps.2 rest
        (ps.1 :: prest.1, prest.2)
    termination_by ss => 2 * sizeOf ss + 1

  def aliasPropCases (sigma : PEnv) :
      List (Literal × Block Op) → List (Literal × Block Op)
    | [] => []
    | (l, body) :: rest =>
        (l, (aliasPropStmts sigma body).1) :: aliasPropCases sigma rest
    termination_by cases => 2 * sizeOf cases + 1

  def aliasPropDflt (sigma : PEnv) :
      Option (Block Op) → Option (Block Op)
    | none => none
    | some body => some (aliasPropStmts sigma body).1
    termination_by dflt => 2 * sizeOf dflt + 1
  decreasing_by
    all_goals simp_wf
end

mutual
  def forwardAliasStmt (source copy : Ident) : Stmt Op → Stmt Op × Bool × Bool
    | .block body =>
        let (body', keep, changed) := forwardAliasStmts source copy body
        (.block body', keep, changed)
    | s@(.funDef _ _ _ _) => (s, true, false)
    | .letDecl xs val =>
        let val' := val.map (useAliasExpr source copy)
        (.letDecl xs val', !xs.contains source && !xs.contains copy,
          val.any (exprMentions source))
    | s@(.assign xs e) =>
        let e' := useAliasExpr source copy e
        let keep := aliasSelfAssign copy s ||
          (!xs.contains source && !xs.contains copy)
        (.assign xs e', keep, exprMentions source e)
    | .cond c body =>
        let (body', keep, changed) := forwardAliasStmts source copy body
        (.cond (useAliasExpr source copy c) body', keep,
          exprMentions source c || changed)
    | .switch c cases dflt =>
        let (cases', changedCases) := forwardAliasCases source copy cases
        let (dflt', changedDflt) := forwardAliasDflt source copy dflt
        let writes := writeSetStmt (.switch c cases dflt)
        (.switch (useAliasExpr source copy c) cases' dflt',
          !writes.contains source && !writes.contains copy,
          exprMentions source c || changedCases || changedDflt)
    | .forLoop init c post body =>
        let (init', _, changedInit) := forwardAliasStmts source copy init
        let (post', _, changedPost) := forwardAliasStmts source copy post
        let (body', _, changedBody) := forwardAliasStmts source copy body
        let writes := writeSetStmt (.forLoop init c post body)
        (.forLoop init' (useAliasExpr source copy c) post' body',
          !writes.contains source && !writes.contains copy,
          changedInit || exprMentions source c || changedPost || changedBody)
    | .exprStmt e =>
        (.exprStmt (useAliasExpr source copy e), true, exprMentions source e)
    | .break => (.break, true, false)
    | .continue => (.continue, true, false)
    | .leave => (.leave, true, false)
    termination_by s => 2 * sizeOf s

  def forwardAliasStmts (source copy : Ident) : Block Op → Block Op × Bool × Bool
    | [] => ([], true, false)
    | s :: rest =>
        let (s', keep, changed) := forwardAliasStmt source copy s
        if keep then
          let (rest', keep', changedRest) := forwardAliasStmts source copy rest
          (s' :: rest', keep', changed || changedRest)
        else (s' :: rest, false, changed)
    termination_by ss => 2 * sizeOf ss + 1

  def forwardAliasCases (source copy : Ident) :
      List (Literal × Block Op) → List (Literal × Block Op) × Bool
    | [] => ([], false)
    | (l, body) :: rest =>
        let (body', _, changedBody) := forwardAliasStmts source copy body
        let (rest', changedRest) := forwardAliasCases source copy rest
        ((l, body') :: rest', changedBody || changedRest)
    termination_by cases => 2 * sizeOf cases + 1

  def forwardAliasDflt (source copy : Ident) :
      Option (Block Op) → Option (Block Op) × Bool
    | none => (none, false)
    | some body =>
        let (body', _, changed) := forwardAliasStmts source copy body
        (some body', changed)
    termination_by dflt => 2 * sizeOf dflt + 1

  decreasing_by
    all_goals simp_wf
end

mutual
  def aliasOneStmt (layout : List Ident) : Stmt Op → Option (Stmt Op)
    | .block body => (.block ·) <$> aliasOneStmts layout body
    | .funDef _ _ _ _ => none
    | .cond c body => (.cond c ·) <$> aliasOneStmts layout body
    | .switch c cases dflt =>
        match aliasOneCases layout cases with
        | some cases' => some (.switch c cases' dflt)
        | none =>
            match dflt with
            | some body =>
                (fun body' => .switch c cases (some body')) <$>
                  aliasOneStmts layout body
            | none => none
    | .forLoop init c post body =>
        let loopLayout := layoutAfter layout init
        match aliasOneStmts loopLayout post with
        | some post' => some (.forLoop init c post' body)
        | none => (.forLoop init c post ·) <$> aliasOneStmts loopLayout body
    | _ => none
    termination_by s => 2 * sizeOf s

  def aliasOneStmts (layout : List Ident) : Block Op → Option (Block Op)
    | [] => none
    | s@(.letDecl [copy] (some (.var source))) :: rest =>
        if copy != source && layout.contains source then
          let (rest', _, changed) := forwardAliasStmts source copy rest
          if changed then some (s :: rest')
          else (s :: ·) <$> aliasOneStmts (copy :: layout) rest
        else (s :: ·) <$> aliasOneStmts (copy :: layout) rest
    | .assign [copy] (.var source) :: rest =>
        match layout.findIdx? (fun x => x = copy),
            layout.findIdx? (fun x => x = source) with
        | some aliasDepth, some sourceDepth =>
            if copy != source && aliasDepth < sourceDepth then
              let (rest', _, changed) := forwardAliasStmts source copy rest
              if changed then some (.assign [copy] (.var source) :: rest')
              else (.assign [copy] (.var source) :: ·) <$>
                aliasOneStmts layout rest
            else if copy != source && sourceDepth < aliasDepth then
              let (rest', _, changed) := forwardAliasStmts copy source rest
              if changed then some (.assign [copy] (.var source) :: rest')
              else (.assign [copy] (.var source) :: ·) <$>
                aliasOneStmts layout rest
            else (.assign [copy] (.var source) :: ·) <$>
              aliasOneStmts layout rest
        | _, _ => (.assign [copy] (.var source) :: ·) <$>
            aliasOneStmts layout rest
    | s :: rest =>
        match aliasOneStmt layout s with
        | some s' => some (s' :: rest)
        | none =>
            let layout' := match s with
              | .letDecl xs _ => xs ++ layout
              | _ => layout
            (s :: ·) <$> aliasOneStmts layout' rest
    termination_by ss => 2 * sizeOf ss + 1

  def aliasOneCases (layout : List Ident) :
      List (Literal × Block Op) → Option (List (Literal × Block Op))
    | [] => none
    | (l, body) :: rest =>
        match aliasOneStmts layout body with
        | some body' => some ((l, body') :: rest)
        | none => ((l, body) :: ·) <$> aliasOneCases layout rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def iterateAliases : Nat → Block Op → Block Op
  | 0, body => body
  | n + 1, body =>
      match aliasOneStmts [] body with
      | some body' => iterateAliases n body'
      | none => body

/-! ### Dominator live-range splitting

When a value that is reachable at a region entry becomes unreachable after
region-local declarations, split its live range at that entry. The fresh
shadow occupies the top slot throughout an inner block; normal exit copies a
written value back only after all inner locals have been restored. -/

mutual
  def firstDeepExpr (Phi : FMap) (entry layout : List Ident) (off : Nat) :
      Expr Op → Option Ident
    | .lit _ => none
    | .var x =>
        match layout.findIdx? (fun y => y = x) with
        | some idx => if entry.contains x && 16 ≤ off + idx then some x else none
        | none => none
    | .builtin _ args => firstDeepArgs Phi entry layout off args
    | .call f args =>
        match lookupF Phi f with
        | some (info, _) => firstDeepArgs Phi entry layout (off + 1 + info.rets) args
        | none => none

  def firstDeepArgs (Phi : FMap) (entry layout : List Ident) (off : Nat) :
      List (Expr Op) → Option Ident
    | [] => none
    | e :: rest => firstDeepArgs Phi entry layout off rest <|>
        firstDeepExpr Phi entry layout (off + rest.length) e
end

mutual
  def firstDeepStmt (Phi : FMap) (entry layout : List Ident) :
      Stmt Op → Option Ident
    | .block body => firstDeepStmts Phi entry layout body
    | .funDef _ _ _ _ => none
    | .letDecl _ val => val.bind (firstDeepExpr Phi entry layout 0)
    | .assign xs e =>
        firstDeepExpr Phi entry layout 0 e <|> xs.zipIdx.findSome? fun (x, i) =>
          match layout.findIdx? (fun y => y = x) with
          | some idx =>
              if entry.contains x && 16 ≤ idx + xs.length - i - 1 then some x
              else none
          | none => none
    | .exprStmt e => firstDeepExpr Phi entry layout 0 e
    | .cond c body => firstDeepExpr Phi entry layout 0 c <|>
        firstDeepStmts Phi entry layout body
    | .switch c cases dflt => firstDeepExpr Phi entry layout 0 c <|>
        firstDeepCases Phi entry layout cases <|>
        firstDeepDflt Phi entry layout dflt
    | .forLoop init c post body =>
        let (scope, _) := hoistInfos 0 init
        let Phi' := scope :: Phi
        let loopLayout := layoutAfter layout init
        firstDeepStmts Phi entry layout init <|>
          firstDeepExpr Phi' entry loopLayout 0 c <|>
          firstDeepStmts Phi' entry loopLayout body <|>
          firstDeepStmts Phi' entry loopLayout post
    | .break | .continue | .leave => none
    termination_by s => 2 * sizeOf s

  def firstDeepStmts (Phi : FMap) (entry layout : List Ident) :
      Block Op → Option Ident
    | [] => none
    | s :: rest =>
        firstDeepStmt Phi entry layout s <|>
          firstDeepStmts Phi entry
            (match s with | .letDecl xs _ => xs ++ layout | _ => layout) rest
    termination_by ss => 2 * sizeOf ss + 1

  def firstDeepCases (Phi : FMap) (entry layout : List Ident) :
      List (Literal × Block Op) → Option Ident
    | [] => none
    | (_, body) :: rest => firstDeepStmts Phi entry layout body <|>
        firstDeepCases Phi entry layout rest
    termination_by cases => 2 * sizeOf cases + 1

  def firstDeepDflt (Phi : FMap) (entry layout : List Ident) :
      Option (Block Op) → Option Ident
    | none => none
    | some body => firstDeepStmts Phi entry layout body
    termination_by dflt => 2 * sizeOf dflt + 1
  decreasing_by
    all_goals simp_wf
end

mutual
  def writesStmt (x : Ident) : Stmt Op → Bool
    | .block body | .cond _ body => writesStmts x body
    | .funDef _ _ _ _ => false
    | .letDecl xs _ | .assign xs _ => xs.contains x
    | .switch _ cases dflt => writesCases x cases || writesDflt x dflt
    | .forLoop init _ post body =>
        writesStmts x init || writesStmts x post || writesStmts x body
    | _ => false
    termination_by s => 2 * sizeOf s

  def writesStmts (x : Ident) : Block Op → Bool
    | [] => false
    | s :: rest => writesStmt x s || writesStmts x rest
    termination_by ss => 2 * sizeOf ss + 1

  def writesCases (x : Ident) : List (Literal × Block Op) → Bool
    | [] => false
    | (_, body) :: rest => writesStmts x body || writesCases x rest
    termination_by cases => 2 * sizeOf cases + 1

  def writesDflt (x : Ident) : Option (Block Op) → Bool
    | none => false
    | some body => writesStmts x body
    termination_by dflt => 2 * sizeOf dflt + 1
  decreasing_by
    all_goals simp_wf
end

mutual
  def hasNonlocalStmt : Stmt Op → Bool
    | .block body | .cond _ body => hasNonlocalStmts body
    | .funDef _ _ _ _ => false
    | .switch _ cases dflt => hasNonlocalCases cases || hasNonlocalDflt dflt
    | .forLoop init _ post body => hasNonlocalStmts init ||
        hasNonlocalStmts post || hasNonlocalStmts body
    | .break | .continue | .leave => true
    | _ => false
    termination_by s => 2 * sizeOf s

  def hasNonlocalStmts : Block Op → Bool
    | [] => false
    | s :: rest => hasNonlocalStmt s || hasNonlocalStmts rest
    termination_by ss => 2 * sizeOf ss + 1

  def hasNonlocalCases : List (Literal × Block Op) → Bool
    | [] => false
    | (_, body) :: rest => hasNonlocalStmts body || hasNonlocalCases rest
    termination_by cases => 2 * sizeOf cases + 1

  def hasNonlocalDflt : Option (Block Op) → Bool
    | none => false
    | some body => hasNonlocalStmts body
    termination_by dflt => 2 * sizeOf dflt + 1
  decreasing_by
    all_goals simp_wf
end

def shadowRegionHere (P : String) (Phi : FMap) (layout : List Ident)
    (body : Block Op) : Option (Block Op) := do
  let source ← firstDeepStmts Phi layout layout body
  let idx ← layout.findIdx? (fun y => y = source)
  let shadow := P ++ "range"
  let written := writesStmts source body
  if 16 ≤ idx || (written && 15 ≤ idx) || hasDirectFun body ||
      hasNonlocalStmts body then none else
  let renamed := renameStmts [(source, shadow)] body
  if (firstDeepStmts Phi [shadow] (shadow :: layout) renamed).isSome then none else
  let exit := if written then [.assign [source] (.var shadow)] else []
  some [.block ([.letDecl [shadow] (some (.var source)), .block renamed] ++ exit)]

mutual
  def shadowOneRegionStmt (P : String) (Phi : FMap) (layout : List Ident) :
      Stmt Op → Option (Stmt Op)
    | .block body => (.block ·) <$> shadowOneRegionStmts P Phi layout body
    | .funDef f ps rs body =>
        (.funDef f ps rs ·) <$> shadowOneRegionStmts P Phi (ps ++ rs) body
    | .cond c body => (.cond c ·) <$> shadowOneRegionStmts P Phi layout body
    | .switch c cases dflt =>
        match shadowOneRegionCases P Phi layout cases with
        | some cases' => some (.switch c cases' dflt)
        | none =>
            match dflt with
            | some body =>
                (fun body' => .switch c cases (some body')) <$>
                  shadowOneRegionStmts P Phi layout body
            | none => none
    | .forLoop init c post body =>
        let (scope, _) := hoistInfos 0 init
        let Phi' := scope :: Phi
        let loopLayout := layoutAfter layout init
        match shadowOneRegionStmts P Phi' loopLayout post with
        | some post' => some (.forLoop init c post' body)
        | none => (.forLoop init c post ·) <$>
            shadowOneRegionStmts P Phi' loopLayout body
    | _ => none
    termination_by s => 2 * sizeOf s

  def shadowOneRegionStmts (P : String) (Phi : FMap) (layout : List Ident) :
      Block Op → Option (Block Op)
    | [] => none
    | s :: rest =>
        match shadowOneRegionStmt P Phi layout s with
        | some s' => some (s' :: rest)
        | none =>
            let layout' := match s with
              | .letDecl xs _ => xs ++ layout
              | _ => layout
            match shadowOneRegionStmts P Phi layout' rest with
            | some rest' => some (s :: rest')
            | none => shadowRegionHere P Phi layout (s :: rest)
    termination_by ss => 2 * sizeOf ss + 1

  def shadowOneRegionCases (P : String) (Phi : FMap) (layout : List Ident) :
      List (Literal × Block Op) → Option (List (Literal × Block Op))
    | [] => none
    | (lit, body) :: rest =>
        match shadowOneRegionStmts P Phi layout body with
        | some body' => some ((lit, body') :: rest)
        | none => ((lit, body) :: ·) <$> shadowOneRegionCases P Phi layout rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def iterateRegionRangesWith : Nat → String → FMap → Block Op → Block Op
  | 0, _, _, body => body
  | n + 1, P, Phi, body =>
      match shadowOneRegionStmts P Phi [] body with
      | some body' => iterateRegionRangesWith n P Phi body'
      | none => body

def iterateRegionRanges (fuel : Nat) (body : Block Op) : Block Op :=
  match freshPrefix (stmtsIdents body) with
  | none => body
  | some P =>
      let (scope, _) := hoistInfos 0 body
      iterateRegionRangesWith fuel P [scope] body

/-! ### One-rewrite allocator

The proof-facing driver performs one coalescing rewrite at a time.  Iterating
that verified local equivalence reaches the same linear-scan fixed point while
making soundness compositional instead of requiring a global many-slot
simulation invariant. -/

mutual
  def reuseOneStmt (layout : List Ident) : Stmt Op → Option (Stmt Op)
    | .block body => (.block ·) <$> reuseOneStmts layout [] body
    | .funDef f ps rs body =>
        (.funDef f ps rs ·) <$> reuseOneStmts (ps ++ rs) [] body
    | .cond c body => (.cond c ·) <$> reuseOneStmts layout [] body
    | .switch c cases dflt =>
        match reuseOneCases layout cases with
        | some cases' => some (.switch c cases' dflt)
        | none =>
            match dflt with
            | some body =>
                match reuseOneStmts layout [] body with
                | some body' => some (.switch c cases (some body'))
                | none => none
            | none => none
    | .forLoop init c post body =>
        match reuseOneStmts layout [] post with
        | some post' => some (.forLoop init c post' body)
        | none => (.forLoop init c post ·) <$> reuseOneStmts layout [] body
    | _ => none
    termination_by s => 2 * sizeOf s

  def reuseOneStmts (layout owned : List Ident) : Block Op → Option (Block Op)
    | [] => none
    | .letDecl ys val :: rest =>
        match ys with
        | [y] =>
            let e := val.getD (.lit (.number 0))
            match reusableSlot layout owned y e rest with
            | some x =>
                some (.assign [x] e :: renameStmts [(y, x)] rest)
            | none =>
                (.letDecl [y] val :: ·) <$>
                  reuseOneStmts (y :: layout) (y :: owned) rest
        | _ =>
            (.letDecl ys val :: ·) <$>
              reuseOneStmts (ys ++ layout) (ys ++ owned) rest
    | s :: rest =>
        match reuseOneStmt layout s with
        | some s' => some (s' :: rest)
        | none => (s :: ·) <$> reuseOneStmts layout owned rest
    termination_by ss => 2 * sizeOf ss + 1

  def reuseOneCases (layout : List Ident) :
      List (Literal × Block Op) → Option (List (Literal × Block Op))
    | [] => none
    | (l, b) :: cases =>
        match reuseOneStmts layout [] b with
        | some b' => some ((l, b') :: cases)
        | none => ((l, b) :: ·) <$> reuseOneCases layout cases
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def iterateStackLayoutFrom : Nat → List Ident → Block Op → Block Op
  | 0, _, b => b
  | n + 1, layout, b =>
      match reuseOneStmts layout [] b with
      | some b' => iterateStackLayoutFrom n layout b'
      | none => b

def iterateStackLayout (n : Nat) (b : Block Op) : Block Op :=
  iterateStackLayoutFrom n [] b

namespace StackV2

mutual
  def stmtReads (x : Ident) : Stmt Op → Bool
    | .block body => stmtsRead x body
    | .funDef _ _ _ _ => false
    | .letDecl _ val => val.any (exprMentions x)
    | .assign _ e | .exprStmt e => exprMentions x e
    | .cond c body => exprMentions x c || stmtsRead x body
    | .switch c cases dflt =>
        exprMentions x c || casesRead x cases || optBlockReads x dflt
    | .forLoop init c post body =>
        stmtsRead x init || exprMentions x c ||
          stmtsRead x post || stmtsRead x body
    | .break | .continue | .leave => false

  def stmtsRead (x : Ident) : Block Op → Bool
    | [] => false
    | .assign xs e :: rest =>
        exprMentions x e || (!xs.contains x && stmtsRead x rest)
    | .letDecl xs val :: rest =>
        val.any (exprMentions x) || (!xs.contains x && stmtsRead x rest)
    | s :: rest => stmtReads x s || stmtsRead x rest

  def casesRead (x : Ident) : List (Literal × Block Op) → Bool
    | [] => false
    | (_, body) :: rest => stmtsRead x body || casesRead x rest

  def optBlockReads (x : Ident) : Option (Block Op) → Bool
    | none => false
    | some body => stmtsRead x body
end

def valueLiveIn (x : Ident) (body : Block Op) : Bool := stmtsRead x body

def crossLayoutAfter := layoutAfter

mutual
  def hasEscapingControlStmt : Stmt Op → Bool
    | .block body | .cond _ body => hasEscapingControlStmts body
    | .switch _ cases dflt => hasEscapingControlCases cases ||
        match dflt with
        | none => false
        | some body => hasEscapingControlStmts body
    | .forLoop _ _ _ _ | .funDef _ _ _ _ => false
    | .break | .continue => true
    | _ => false
    termination_by s => 2 * sizeOf s

  def hasEscapingControlStmts : Block Op → Bool
    | [] => false
    | s :: rest => hasEscapingControlStmt s || hasEscapingControlStmts rest
    termination_by ss => 2 * sizeOf ss + 1

  def hasEscapingControlCases : List (Literal × Block Op) → Bool
    | [] => false
    | (_, body) :: rest =>
        hasEscapingControlStmts body || hasEscapingControlCases rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

/-! ### Shallow available-copy forwarding

If a shallow local is assigned the current value of a deeper binding, reads of
the deep binding may use that local until either side is written or shadowed.
This is ordinary available-copy dataflow, oriented in the register-allocation
direction (deep to shallow), complementary to `Propagate`'s expression-
simplification direction. -/

mutual
  def useAliasExpr (source copy : Ident) : Expr Op → Expr Op
    | .lit l => .lit l
    | .var x => .var (if x = source then copy else x)
    | .builtin op args => .builtin op (useAliasArgs source copy args)
    | .call f args => .call f (useAliasArgs source copy args)

  def useAliasArgs (source copy : Ident) : List (Expr Op) → List (Expr Op)
    | [] => []
    | e :: rest => useAliasExpr source copy e :: useAliasArgs source copy rest
end

def aliasSelfAssign (copy : Ident) : Stmt Op → Bool
  | .assign [x] (.var y) => x = copy && y = copy
  | _ => false

mutual
  def forwardAliasStmt (source copy : Ident) : Stmt Op → Stmt Op × Bool × Bool
    | .block body =>
        let (body', _, changed) := forwardAliasStmts source copy body
        let writes := writeSetStmts body
        (.block body', !writes.contains source && !writes.contains copy, changed)
    | s@(.funDef _ _ _ _) => (s, true, false)
    | .letDecl xs val =>
        let val' := val.map (useAliasExpr source copy)
        (.letDecl xs val', !xs.contains source && !xs.contains copy,
          val.any (exprMentions source))
    | s@(.assign xs e) =>
        let e' := useAliasExpr source copy e
        let keep := aliasSelfAssign copy s ||
          (!xs.contains source && !xs.contains copy)
        (.assign xs e', keep, exprMentions source e)
    | .cond c body =>
        let (body', _, changed) := forwardAliasStmts source copy body
        let writes := writeSetStmts body
        (.cond (useAliasExpr source copy c) body',
          !writes.contains source && !writes.contains copy,
          exprMentions source c || changed)
    | s@(.switch _ _ _) => (s, false, false)
    | s@(.forLoop _ _ _ _) => (s, false, false)
    | .exprStmt e =>
        (.exprStmt (useAliasExpr source copy e), true, exprMentions source e)
    | .break => (.break, true, false)
    | .continue => (.continue, true, false)
    | .leave => (.leave, true, false)
    termination_by s => 2 * sizeOf s

  def forwardAliasStmts (source copy : Ident) : Block Op → Block Op × Bool × Bool
    | [] => ([], true, false)
    | s :: rest =>
        let (s', keep, changed) := forwardAliasStmt source copy s
        if keep then
          let (rest', keep', changedRest) := forwardAliasStmts source copy rest
          (s' :: rest', keep', changed || changedRest)
        else (s' :: rest, false, changed)
    termination_by ss => 2 * sizeOf ss + 1

  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def aliasOneStmt (_layout : List Ident) : Stmt Op → Option (Stmt Op)
    | _ => none

  def aliasOneStmts (layout : List Ident) : Block Op → Option (Block Op)
    | [] => none
    | .letDecl xs val :: rest =>
        match xs, val with
        | [copy], some (.var source) =>
            let s := Stmt.letDecl [copy] (some (.var source))
            if copy != source && layout.contains source then
              let (rest', _, changed) := forwardAliasStmts source copy rest
              if changed then some (s :: rest')
              else (s :: ·) <$> aliasOneStmts (copy :: layout) rest
            else (s :: ·) <$> aliasOneStmts (copy :: layout) rest
        | _, _ =>
            (.letDecl xs val :: ·) <$> aliasOneStmts (xs ++ layout) rest
    | .assign xs e :: rest =>
        match xs, e with
        | [copy], .var source =>
            match layout.findIdx? (fun x => x = copy),
                layout.findIdx? (fun x => x = source) with
            | some aliasDepth, some sourceDepth =>
                if copy != source && aliasDepth < sourceDepth then
                  let (rest', _, changed) := forwardAliasStmts source copy rest
                  if changed then
                    some (.assign [copy] (.var source) :: rest')
                  else
                    (.assign [copy] (.var source) :: ·) <$> aliasOneStmts layout rest
                else if copy != source && sourceDepth < aliasDepth then
                  let (rest', _, changed) := forwardAliasStmts copy source rest
                  if changed then
                    some (.assign [copy] (.var source) :: rest')
                  else
                    (.assign [copy] (.var source) :: ·) <$> aliasOneStmts layout rest
                else
                  (.assign [copy] (.var source) :: ·) <$> aliasOneStmts layout rest
            | _, _ =>
                (.assign [copy] (.var source) :: ·) <$> aliasOneStmts layout rest
        | _, _ =>
            (.assign xs e :: ·) <$> aliasOneStmts layout rest
    | s :: rest =>
        (s :: ·) <$> aliasOneStmts layout rest
    termination_by ss => 2 * sizeOf ss + 1

  def aliasOneCases (layout : List Ident) :
      List (Literal × Block Op) → Option (List (Literal × Block Op))
    | [] => none
    | (l, body) :: rest =>
        match aliasOneStmts layout body with
        | some body' => some ((l, body') :: rest)
        | none => ((l, body) :: ·) <$> aliasOneCases layout rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
end

def iterateAliases : Nat → Block Op → Block Op
  | 0, b => b
  | n + 1, b =>
      match aliasOneStmts [] b with
      | some b' => iterateAliases n b'
      | none => b

/-! ### Liveness-guided prefix regions

For a deep assignment in a long linear frame, keep only declarations live at
the assignment or in its continuation outside a nested prefix region.  Their
zero declarations dominate the region; their original initializers stay at
the original program points as assignments.  All other prefix locals die when
the nested block restores, before the deep destination is written. -/

def groupLiveAt (xs : List Ident) (e : Expr Op) (suffix : Block Op) : Bool :=
  xs.any fun x => exprMentions x e || stmtsMentions x suffix

def directLiveNames (e : Expr Op) (suffix : Block Op) : Block Op → List Ident
  | [] => []
  | .letDecl xs _ :: rest =>
      (if groupLiveAt xs e suffix then xs else []) ++
        directLiveNames e suffix rest
  | _ :: rest => directLiveNames e suffix rest

def exprMentionsAny (xs : List Ident) (e : Expr Op) : Bool :=
  xs.any fun x => exprMentions x e

def declDominates (x : Ident) : Block Op → Bool
  | [] => false
  | .letDecl xs val :: rest =>
      if xs.contains x then !val.any (exprMentions x)
      else !stmtMentions x (.letDecl xs val) && declDominates x rest
  | s :: rest => !stmtMentions x s && declDominates x rest

def promotePrefix (live : List Ident) :
    Block Op → Option (Block Op × Block Op)
  | [] => some ([], [])
  | s@(.letDecl xs val) :: rest => do
      let (outer, inner) ← promotePrefix live rest
      if xs.any live.contains then
        if !val.any (exprMentionsAny xs) then
          let init := match val with
            | none => []
            | some e => [.assign xs e]
          some (.letDecl xs none :: outer, init ++ inner)
        else none
      else some (outer, s :: inner)
  | s :: rest => do
      let (outer, inner) ← promotePrefix live rest
      some (outer, s :: inner)

def regionTargetsFit (layout xs : List Ident) : Bool :=
  xs.zipIdx.all fun (x, i) =>
    match layout.findIdx? (fun y => y = x) with
    | some idx => idx + (xs.length - i - 1) < 16
    | none => false

def splitAtDeadDecl (live : List Ident) :
    Block Op → Option (Block Op × Block Op)
  | [] => none
  | ss@(.letDecl xs val :: rest) =>
      if xs.any live.contains then do
        let (head, tail) ← splitAtDeadDecl live rest
        some (.letDecl xs val :: head, tail)
      else some ([], ss)
  | s :: rest => do
      let (head, tail) ← splitAtDeadDecl live rest
      some (s :: head, tail)

def prefixRegionSearch (entry : List Ident) :
    Block Op → List Ident → Block Op → Option (Block Op)
  | _pre, _, [] => none
  | pre, layout, s@(.assign xs e) :: suffix =>
      if !regionTargetsFit layout xs && xs.all entry.contains &&
          !hasDirectFun pre then
        let live := directLiveNames e suffix pre
        if !live.isEmpty && live.Nodup &&
            live.all (fun x => !entry.contains x && !stmtsDeclare x suffix &&
              declDominates x pre) then
          match splitAtDeadDecl live pre with
          | some (head, region) =>
            match promotePrefix live region with
            | some (outer, inner) =>
                some (head ++ outer ++ [.block inner, s] ++ suffix)
            | none => prefixRegionSearch entry (pre ++ [s]) layout suffix
          | none => prefixRegionSearch entry (pre ++ [s]) layout suffix
        else prefixRegionSearch entry (pre ++ [s]) layout suffix
      else prefixRegionSearch entry (pre ++ [s]) layout suffix
  | pre, layout, s :: suffix =>
      let layout' := match s with
        | .letDecl ys _ => ys ++ layout
        | _ => layout
      prefixRegionSearch entry (pre ++ [s]) layout' suffix
  termination_by _pre _layout rest => rest.length

def prefixRegionHere (entry : List Ident) (ss : Block Op) : Option (Block Op) :=
  prefixRegionSearch entry [] entry ss

mutual
  def prefixOneStmt (layout : List Ident) : Stmt Op → Option (Stmt Op)
    | .block body => (.block ·) <$> prefixOneStmts layout body
    | .funDef f ps rs body =>
        (.funDef f ps rs ·) <$> prefixOneStmts (ps ++ rs) body
    | .cond c body => (.cond c ·) <$> prefixOneStmts layout body
    | .switch c cases dflt =>
        match prefixOneCases layout cases with
        | some cases' => some (.switch c cases' dflt)
        | none =>
            match dflt with
            | some body => (.switch c cases ·) <$> prefixOneStmts layout body
            | none => none
    | .forLoop init c post body =>
        let loopLayout := crossLayoutAfter layout init
        match prefixOneStmts loopLayout post with
        | some post' => some (.forLoop init c post' body)
        | none => (.forLoop init c post ·) <$> prefixOneStmts loopLayout body
    | _ => none
    termination_by s => 2 * sizeOf s

  def prefixOneStmts (entry : List Ident) (ss : Block Op) : Option (Block Op) :=
    match prefixRegionHere entry ss with
    | some ss' => some ss'
    | none =>
        match ss with
        | [] => none
        | s :: rest =>
            match prefixOneStmt entry s with
            | some s' => some (s' :: rest)
            | none =>
                let entry' := match s with
                  | .letDecl xs _ => xs ++ entry
                  | _ => entry
                (s :: ·) <$> prefixOneStmts entry' rest
    termination_by 2 * sizeOf ss + 1

  def prefixOneCases (layout : List Ident) :
      List (Literal × Block Op) → Option (List (Literal × Block Op))
    | [] => none
    | (l, body) :: rest =>
        match prefixOneStmts layout body with
        | some body' => some ((l, body') :: rest)
        | none => ((l, body) :: ·) <$> prefixOneCases layout rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def iteratePrefixRegions : Nat → Block Op → Block Op
  | 0, b => b
  | n + 1, b =>
      match prefixOneStmts [] b with
      | some b' => iteratePrefixRegions n b'
      | none => b

/-- Apply at most one prefix-region split to each direct function body.  Solc
places generated functions directly in object code blocks; bounding the pass
this way keeps nesting independent of the number of assignments in a large
function. -/
def prefixFunctionStmt : Stmt Op → Stmt Op
  | .funDef f ps rs body =>
      .funDef f ps rs ((prefixRegionHere (ps ++ rs) body).getD body)
  | s => s

def prefixFunctionStmts (body : Block Op) : Block Op :=
  body.map prefixFunctionStmt

/-! ### Loop-region live-range splitting

When a loop body temporarily grows past the reachable stack window, split the
live ranges of entry variables once at the loop header.  All shadows live in
one outer block; the original body runs in an inner block, so its temporary
locals are gone before modified shadows are copied back.  Copies are also
placed on the loop's `break`/`continue` edges.  This is the structured-CFG
form of SSA destruction at a loop-header dominator. -/

def addName (x : Ident) (xs : List Ident) : List Ident :=
  if xs.contains x then xs else x :: xs

mutual
  def deepVarsExpr (Phi : FMap) (entry layout : List Ident) (off : Nat) :
      Expr Op → List Ident
    | .lit _ => []
    | .var x =>
        match layout.findIdx? (fun y => y = x) with
        | some idx => if entry.contains x && 16 ≤ off + idx then [x] else []
        | none => []
    | .builtin _ args => deepVarsArgs Phi entry layout off args
    | .call f args =>
        match lookupF Phi f with
        | some (info, _) => deepVarsArgs Phi entry layout (off + 1 + info.rets) args
        | none => []

  def deepVarsArgs (Phi : FMap) (entry layout : List Ident) (off : Nat) :
      List (Expr Op) → List Ident
    | [] => []
    | e :: rest =>
        (deepVarsArgs Phi entry layout off rest).foldr addName
          (deepVarsExpr Phi entry layout (off + rest.length) e)
end

mutual
  def firstDeepExpr (Phi : FMap) (entry layout : List Ident) (off : Nat) :
      Expr Op → Option Ident
    | .lit _ => none
    | .var x =>
        match layout.findIdx? (fun y => y = x) with
        | some idx => if entry.contains x && 16 ≤ off + idx then some x else none
        | none => none
    | .builtin _ args => firstDeepArgs Phi entry layout off args
    | .call f args =>
        match lookupF Phi f with
        | some (info, _) => firstDeepArgs Phi entry layout (off + 1 + info.rets) args
        | none => none

  def firstDeepArgs (Phi : FMap) (entry layout : List Ident) (off : Nat) :
      List (Expr Op) → Option Ident
    | [] => none
    | e :: rest => firstDeepArgs Phi entry layout off rest <|>
        firstDeepExpr Phi entry layout (off + rest.length) e
end

mutual
  def firstDeepStmt (Phi : FMap) (entry layout : List Ident) :
      Stmt Op → Option Ident
    | .block body => firstDeepStmts Phi entry layout body
    | .funDef _ ps rs body => firstDeepStmts Phi (ps ++ rs) (ps ++ rs) body
    | .letDecl _ val => val.bind (firstDeepExpr Phi entry layout 0)
    | .assign xs e =>
        firstDeepExpr Phi entry layout 0 e <|> xs.zipIdx.findSome? fun (x, i) =>
          match layout.findIdx? (fun y => y = x) with
          | some idx =>
              if entry.contains x && 16 ≤ idx + xs.length - i - 1 then some x
              else none
          | none => none
    | .exprStmt e => firstDeepExpr Phi entry layout 0 e
    | .cond c body => firstDeepExpr Phi entry layout 0 c <|>
        firstDeepStmts Phi entry layout body
    | .switch c cases dflt => firstDeepExpr Phi entry layout 0 c <|>
        firstDeepCases Phi entry layout cases <|>
        firstDeepDflt Phi entry layout dflt
    | .forLoop init c post body =>
        let (scope, _) := hoistInfos 0 init
        let Phi' := scope :: Phi
        let loopLayout := layoutAfter layout init
        firstDeepStmts Phi entry layout init <|>
          firstDeepExpr Phi' entry loopLayout 0 c <|>
          firstDeepStmts Phi' entry loopLayout body <|>
          firstDeepStmts Phi' entry loopLayout post
    | .break | .continue | .leave => none
    termination_by s => 2 * sizeOf s

  def firstDeepStmts (Phi : FMap) (entry layout : List Ident) :
      Block Op → Option Ident
    | [] => none
    | s :: rest =>
        firstDeepStmt Phi entry layout s <|>
          firstDeepStmts Phi entry
            (match s with | .letDecl xs _ => xs ++ layout | _ => layout) rest
    termination_by ss => 2 * sizeOf ss + 1

  def firstDeepCases (Phi : FMap) (entry layout : List Ident) :
      List (Literal × Block Op) → Option Ident
    | [] => none
    | (_, body) :: rest => firstDeepStmts Phi entry layout body <|>
        firstDeepCases Phi entry layout rest
    termination_by cases => 2 * sizeOf cases + 1

  def firstDeepDflt (Phi : FMap) (entry layout : List Ident) :
      Option (Block Op) → Option Ident
    | none => none
    | some body => firstDeepStmts Phi entry layout body
    termination_by dflt => 2 * sizeOf dflt + 1
  decreasing_by
    all_goals simp_wf
end

mutual
  def deepVarsStmt (Phi : FMap) (entry layout : List Ident) :
      Stmt Op → List Ident
    | .block body => deepVarsStmts Phi entry layout body
    | .funDef _ _ _ _ => []
    | .letDecl _ val => val.map (deepVarsExpr Phi entry layout 0) |>.getD []
    | .assign xs e =>
        let targets := xs.zipIdx.foldr (fun (x, i) deep =>
          match layout.findIdx? (fun y => y = x) with
          | some idx =>
              if entry.contains x && 16 ≤ idx + xs.length - i - 1 then
                addName x deep
              else deep
          | none => deep) []
        (deepVarsExpr Phi entry layout 0 e).foldr addName targets
    | .exprStmt e => deepVarsExpr Phi entry layout 0 e
    | .cond c body =>
        (deepVarsStmts Phi entry layout body).foldr addName
          (deepVarsExpr Phi entry layout 0 c)
    | .switch c cases dflt =>
        let fromCases := deepVarsCases Phi entry layout cases
        let fromDefault := match dflt with
          | some body => deepVarsStmts Phi entry layout body
          | none => []
        fromDefault.foldr addName
          (fromCases.foldr addName (deepVarsExpr Phi entry layout 0 c))
    | .forLoop init c post body =>
        let (scope, _) := hoistInfos 0 init
        let Phi' := scope :: Phi
        let loopLayout := layoutAfter layout init
        let a := deepVarsStmts Phi entry layout init
        let b := deepVarsExpr Phi' entry loopLayout 0 c
        let p := deepVarsStmts Phi' entry loopLayout post
        let q := deepVarsStmts Phi' entry loopLayout body
        q.foldr addName (p.foldr addName (b.foldr addName a))
    | .break | .continue | .leave => []
    termination_by s => 2 * sizeOf s

  def deepVarsStmts (Phi : FMap) (entry layout : List Ident) :
      Block Op → List Ident
    | [] => []
    | s :: rest =>
        let here := deepVarsStmt Phi entry layout s
        let layout' := match s with
          | .letDecl xs _ => xs ++ layout
          | _ => layout
        (deepVarsStmts Phi entry layout' rest).foldr addName here
    termination_by ss => 2 * sizeOf ss + 1

  def deepVarsCases (Phi : FMap) (entry layout : List Ident) :
      List (Literal × Block Op) → List Ident
    | [] => []
    | (_, body) :: rest =>
        (deepVarsCases Phi entry layout rest).foldr addName
          (deepVarsStmts Phi entry layout body)
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def writesStmt (x : Ident) : Stmt Op → Bool
    | .block body | .cond _ body => writesStmts x body
    | .funDef _ _ _ _ => false
    | .letDecl xs _ | .assign xs _ => xs.contains x
    | .switch _ cases dflt => writesCases x cases ||
        match dflt with
        | some body => writesStmts x body
        | none => false
    | .forLoop init _ post body =>
        writesStmts x init || writesStmts x post || writesStmts x body
    | _ => false
    termination_by s => 2 * sizeOf s

  def writesStmts (x : Ident) : Block Op → Bool
    | [] => false
    | s :: rest => writesStmt x s || writesStmts x rest
    termination_by ss => 2 * sizeOf ss + 1

  def writesCases (x : Ident) : List (Literal × Block Op) → Bool
    | [] => false
    | (_, body) :: rest => writesStmts x body || writesCases x rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def shadowNames (P : String) (n : Nat) : List Ident :=
  (List.range n).map fun i => s!"{P}s{i}"

def refreshNames (P : String) (n : Nat) : List Ident :=
  (List.range n).map fun i => s!"{P}t{i}"

def refreshClosure (fuel : Nat) (P : String) (Phi : FMap)
    (layout shadows : List Ident) (body : Block Op) : List Ident → List Ident
  | sources =>
      match fuel with
      | 0 => sources
      | n + 1 =>
          let names := refreshNames P sources.length
          let pairs := sources.zip names
          let renamed := renameStmts pairs body
          let current := names.reverse ++ shadows.reverse ++ layout
          let more := deepVarsStmts Phi shadows current renamed |>.filter fun x =>
            !sources.contains x
          if more.isEmpty then sources
          else refreshClosure n P Phi layout shadows body
            (more.foldr addName sources)

def shadowClosure (fuel : Nat) (P : String) (Phi : FMap)
    (layout : List Ident) (body : Block Op) : List Ident → List Ident
  | sources =>
      match fuel with
      | 0 => sources
      | n + 1 =>
          let names := shadowNames P sources.length
          let pairs := sources.zip names
          let renamed := renameStmts (pairs.map fun p => (p.1, p.2)) body
          let current := names.reverse ++ layout
          let more := deepVarsStmts Phi layout current renamed |>.filter fun x =>
            !sources.contains x &&
              (!writesStmts x body ||
                match layout.findIdx? (fun y => y = x) with
                | some idx => sources.length + 1 + idx < 16
                | none => false)
          if more.isEmpty then sources
          else shadowClosure n P Phi layout body (more.foldr addName sources)

/-- Extend an already useful set of loop shadows only when the rewritten loop
body still has a deep access to either a stable entry value or a scratch value
whose old value is dead.  Adding one value and recomputing is important: every
shadow changes all subsequent stack depths, so taking a batch closure can
manufacture pressure that no original use had. -/
def stableShadowClosure (fuel : Nat) (P : String) (Phi : FMap)
    (layout : List Ident) (body : Block Op) : List Ident → List Ident
  | sources =>
      match fuel with
      | 0 => sources
      | n + 1 =>
          let names := shadowNames P sources.length
          let pairs := sources.zip names
          let renamed := renameStmts pairs body
          let current := names.reverse ++ layout
          let deep := deepVarsStmts Phi (names ++ layout) current renamed
          match deep.find? fun x => names.contains x with
          | some shadow =>
              match pairs.find? fun p => p.2 = shadow with
              | some (source, _) =>
                  let promoted := sources.erase source ++ [source]
                  if promoted = sources then sources
                  else stableShadowClosure n P Phi layout body promoted
              | none => sources
          | none =>
              match deep.find? fun x =>
                  layout.contains x && !sources.contains x &&
                    (!writesStmts x body || !valueLiveIn x body) with
              | some x =>
                  if sources.length < 16 then
                    stableShadowClosure n P Phi layout body (sources ++ [x])
                  else sources
              | none => sources

mutual
  def maxUseDepthExpr (x : Ident) (Phi : FMap) (layout : List Ident)
      (off : Nat) : Expr Op → Nat
    | .lit _ => 0
    | .var y =>
        if x = y then
          match layout.findIdx? (fun z => z = y) with
          | some idx => off + idx
          | none => 0
        else 0
    | .builtin _ args => maxUseDepthArgs x Phi layout off args
    | .call f args =>
        match lookupF Phi f with
        | some (info, _) => maxUseDepthArgs x Phi layout (off + 1 + info.rets) args
        | none => 0

  def maxUseDepthArgs (x : Ident) (Phi : FMap) (layout : List Ident)
      (off : Nat) : List (Expr Op) → Nat
    | [] => 0
    | e :: rest => max (maxUseDepthArgs x Phi layout off rest)
        (maxUseDepthExpr x Phi layout (off + rest.length) e)
end

mutual
  def maxUseDepthStmt (x : Ident) (Phi : FMap) (layout : List Ident) :
      Stmt Op → Nat
    | .block body => maxUseDepthStmts x Phi layout body
    | .funDef _ _ _ _ => 0
    | .letDecl _ val => val.map (maxUseDepthExpr x Phi layout 0) |>.getD 0
    | .assign xs e =>
        let rhs := maxUseDepthExpr x Phi layout 0 e
        let lhs := xs.zipIdx.foldl (fun acc (y, i) =>
          if x = y then
            match layout.findIdx? (fun z => z = y) with
            | some idx => max acc (idx + xs.length - i - 1)
            | none => acc
          else acc) 0
        max rhs lhs
    | .exprStmt e => maxUseDepthExpr x Phi layout 0 e
    | .cond c body => max (maxUseDepthExpr x Phi layout 0 c)
        (maxUseDepthStmts x Phi layout body)
    | .switch c cases dflt =>
        max (maxUseDepthExpr x Phi layout 0 c)
          (max (maxUseDepthCases x Phi layout cases)
            (maxUseDepthDflt x Phi layout dflt))
    | .forLoop init c post body =>
        let (scope, _) := hoistInfos 0 init
        let Phi' := scope :: Phi
        let loopLayout := layoutAfter layout init
        max (maxUseDepthStmts x Phi layout init)
          (max (maxUseDepthExpr x Phi' loopLayout 0 c)
            (max (maxUseDepthStmts x Phi' loopLayout post)
              (maxUseDepthStmts x Phi' loopLayout body)))
    | .break | .continue | .leave => 0
    termination_by s => 2 * sizeOf s

  def maxUseDepthStmts (x : Ident) (Phi : FMap) (layout : List Ident) :
      Block Op → Nat
    | [] => 0
    | s :: rest =>
        let layout' := match s with
          | .letDecl xs _ => xs ++ layout
          | _ => layout
        max (maxUseDepthStmt x Phi layout s)
          (maxUseDepthStmts x Phi layout' rest)
    termination_by ss => 2 * sizeOf ss + 1

  def maxUseDepthCases (x : Ident) (Phi : FMap) (layout : List Ident) :
      List (Literal × Block Op) → Nat
    | [] => 0
    | (_, body) :: rest => max (maxUseDepthStmts x Phi layout body)
        (maxUseDepthCases x Phi layout rest)
    termination_by cases => 2 * sizeOf cases + 1

  def maxUseDepthDflt (x : Ident) (Phi : FMap) (layout : List Ident) :
      Option (Block Op) → Nat
    | none => 0
    | some body => maxUseDepthStmts x Phi layout body
    termination_by dflt => 2 * sizeOf dflt + 1
  decreasing_by
    all_goals simp_wf
end

def usePressure (x : Ident) (Phi : FMap) (layout : List Ident)
    (body : Block Op) : Nat :=
  let base := layout.findIdx? (fun y => y = x) |>.getD 0
  maxUseDepthStmts x Phi layout body - base

def insertByPressure (Phi : FMap) (layout : List Ident) (body : Block Op)
    (x : Ident) : List Ident → List Ident
  | [] => [x]
  | y :: ys =>
      if usePressure x Phi layout body ≤ usePressure y Phi layout body then
        x :: y :: ys
      else y :: insertByPressure Phi layout body x ys

def sortByPressure (Phi : FMap) (layout : List Ident) (body : Block Op) :
    List Ident → List Ident
  | [] => []
  | x :: xs => insertByPressure Phi layout body x
      (sortByPressure Phi layout body xs)

def copyBacks (pairs : List (Ident × Ident)) : Block Op :=
  pairs.map fun p => .assign [p.1] (.var p.2)

def pickWritableShadows (layout : List Ident) (base : Nat) :
    List Ident → List Ident → List Ident
  | picked, [] => picked
  | picked, x :: rest =>
      match layout.findIdx? (fun y => y = x) with
      | some idx =>
          if base + picked.length + 1 + idx < 16 then
            pickWritableShadows layout base (picked ++ [x]) rest
          else pickWritableShadows layout base picked rest
      | none => pickWritableShadows layout base picked rest

def writesAny (xs : List Ident) (s : Stmt Op) : Bool :=
  xs.any fun x => writesStmt x s

mutual
  def controlsBeforeWritesStmt (xs : List Ident) (dirty : Bool) :
      Stmt Op → Bool
    | .block body | .cond _ body => controlsBeforeWritesStmts xs dirty body
    | .switch _ cases dflt => controlsBeforeWritesCases xs dirty cases &&
        match dflt with
        | some body => controlsBeforeWritesStmts xs dirty body
        | none => true
    | .forLoop _ _ _ _ => true
    | .break | .continue => !dirty
    | _ => true
    termination_by s => 2 * sizeOf s

  def controlsBeforeWritesStmts (xs : List Ident) (dirty : Bool) :
      Block Op → Bool
    | [] => true
    | s :: rest => controlsBeforeWritesStmt xs dirty s &&
        controlsBeforeWritesStmts xs (dirty || writesAny xs s) rest
    termination_by ss => 2 * sizeOf ss + 1

  def controlsBeforeWritesCases (xs : List Ident) (dirty : Bool) :
      List (Literal × Block Op) → Bool
    | [] => true
    | (_, body) :: rest => controlsBeforeWritesStmts xs dirty body &&
        controlsBeforeWritesCases xs dirty rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  /-- Inject copy-backs only for control edges owned by the current loop.
  Nested loops own their own `break`/`continue`; `leave` is conservatively
  rejected by `shadowLoopHere` for now. -/
  def edgeCopiesStmt (copies : Block Op) : Stmt Op → Stmt Op
    | .block body => .block (edgeCopiesStmts copies body)
    | .cond c body => .cond c (edgeCopiesStmts copies body)
    | .switch c cases dflt =>
        .switch c (edgeCopiesCases copies cases)
          (match dflt with
          | some body => some (edgeCopiesStmts copies body)
          | none => none)
    | s@(.forLoop _ _ _ _) => s
    | .break => .block (copies ++ [.break])
    | .continue => .block (copies ++ [.continue])
    | .leave => .block (copies ++ [.leave])
    | s => s
    termination_by s => 2 * sizeOf s

  def edgeCopiesStmts (copies : Block Op) : Block Op → Block Op
    | [] => []
    | s :: rest => edgeCopiesStmt copies s :: edgeCopiesStmts copies rest
    termination_by ss => 2 * sizeOf ss + 1

  def edgeCopiesCases (copies : Block Op) :
      List (Literal × Block Op) → List (Literal × Block Op)
    | [] => []
    | (l, body) :: rest => (l, edgeCopiesStmts copies body) ::
        edgeCopiesCases copies rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def hasLeaveStmt : Stmt Op → Bool
    | .block body | .cond _ body => hasLeaveStmts body
    | .funDef _ _ _ _ => false
    | .switch _ cases dflt => hasLeaveCases cases ||
        match dflt with
        | some body => hasLeaveStmts body
        | none => false
    | .forLoop init _ post body =>
        hasLeaveStmts init || hasLeaveStmts post || hasLeaveStmts body
    | .leave => true
    | _ => false
    termination_by s => 2 * sizeOf s

  def hasLeaveStmts : Block Op → Bool
    | [] => false
    | s :: rest => hasLeaveStmt s || hasLeaveStmts rest
    termination_by ss => 2 * sizeOf ss + 1

  def hasLeaveCases : List (Literal × Block Op) → Bool
    | [] => false
    | (_, body) :: rest => hasLeaveStmts body || hasLeaveCases rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def shadowLoopHere (P : String) (Phi : FMap) (layout : List Ident)
    (body : Block Op) : Option (Block Op) := do
  let initial := (deepVarsStmts Phi layout layout body).reverse
  let closed := shadowClosure 16 P Phi layout body initial
  let stable := layout.reverse.filter fun x =>
    closed.contains x && (!writesStmts x body || !valueLiveIn x body)
  let writable := layout.filter fun x =>
    closed.contains x && writesStmts x body && valueLiveIn x body
  let picked := pickWritableShadows layout stable.length [] writable
  let sources := sortByPressure Phi layout body (stable ++ picked.reverse)
  if sources.isEmpty || !sources.Nodup || hasLeaveStmts body then none else
  let shadows := shadowNames P sources.length
  let basePairs := sources.zip shadows
  let renamedBase := renameStmts (basePairs.map fun p => (p.1, p.2)) body
  let remainingDeep := deepVarsStmts Phi (shadows ++ layout)
    (shadows.reverse ++ layout) renamedBase
  let pairs := basePairs
  let written := pairs.filter fun p =>
    writesStmts p.1 body && valueLiveIn p.1 body
  let writtenSources := written.map Prod.fst
  if !remainingDeep.isEmpty || !written.all (fun p =>
      match layout.findIdx? (fun x => x = p.1) with
      | some idx => shadows.length + idx < 16
      | none => false) ||
      !controlsBeforeWritesStmts writtenSources false body then none else
  let decls := basePairs.map fun p =>
    .letDecl [p.2] (if valueLiveIn p.1 body then some (.var p.1) else none)
  let copies := copyBacks written
  some [.block (decls ++ [.block (edgeCopiesStmts [] renamedBase)] ++ copies)]

mutual
  def shadowLoopsStmt (P : String) (Phi : FMap) (layout : List Ident) :
      Stmt Op → Stmt Op
    | .block body => .block (shadowLoopsStmts P Phi layout body)
    | .funDef f ps rs body =>
        .funDef f ps rs (shadowLoopsStmts P Phi (ps ++ rs) body)
    | .cond c body => .cond c (shadowLoopsStmts P Phi layout body)
    | .switch c cases dflt =>
        .switch c (shadowLoopsCases P Phi layout cases)
          (match dflt with
          | some body => some (shadowLoopsStmts P Phi layout body)
          | none => none)
    | .forLoop init c post body =>
        let (scope, _) := hoistInfos 0 init
        let Phi' := scope :: Phi
        let loopLayout := layoutAfter layout init
        let post' := shadowLoopsStmts P Phi' loopLayout post
        let body' := shadowLoopsStmts P Phi' loopLayout body
        .forLoop init c post' ((shadowLoopHere P Phi' loopLayout body').getD body')
    | s => s
    termination_by s => 2 * sizeOf s

  def shadowLoopsStmts (P : String) (Phi : FMap) (layout : List Ident) :
      Block Op → Block Op
    | [] => []
    | s :: rest =>
        let s' := shadowLoopsStmt P Phi layout s
        let layout' := match s with
          | .letDecl xs _ => xs ++ layout
          | _ => layout
        s' :: shadowLoopsStmts P Phi layout' rest
    termination_by ss => 2 * sizeOf ss + 1

  def shadowLoopsCases (P : String) (Phi : FMap) (layout : List Ident) :
      List (Literal × Block Op) → List (Literal × Block Op)
    | [] => []
    | (l, body) :: rest => (l, shadowLoopsStmts P Phi layout body) ::
        shadowLoopsCases P Phi layout rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def splitLoopRanges (P : String) (b : Block Op) : Block Op :=
  let (scope, _) := hoistInfos 0 b
  shadowLoopsStmts P [scope] [] b

def generatedRangeName (x : Ident) : Bool :=
  x.startsWith "fc" && x.endsWith "_r"

mutual
  def rangeInitsFitStmt (Phi : FMap) (layout : List Ident) : Stmt Op → Bool
    | .block body | .cond _ body => rangeInitsFitStmts Phi layout body
    | .funDef _ _ _ _ => true
    | .letDecl [x] val =>
        if generatedRangeName x then val.all (exprFits Phi layout 0) else true
    | .letDecl _ _ | .assign _ _ | .exprStmt _ | .break | .continue | .leave => true
    | .switch _ cases dflt => rangeInitsFitCases Phi layout cases &&
        rangeInitsFitDflt Phi layout dflt
    | .forLoop init _ post body =>
        let (scope, _) := hoistInfos 0 init
        let Phi' := scope :: Phi
        let loopLayout := layoutAfter layout init
        rangeInitsFitStmts Phi layout init && rangeInitsFitStmts Phi' loopLayout post &&
          rangeInitsFitStmts Phi' loopLayout body
    termination_by s => 2 * sizeOf s

  def rangeInitsFitStmts (Phi : FMap) (layout : List Ident) : Block Op → Bool
    | [] => true
    | s :: rest => rangeInitsFitStmt Phi layout s &&
        rangeInitsFitStmts Phi
          (match s with | .letDecl xs _ => xs ++ layout | _ => layout) rest
    termination_by ss => 2 * sizeOf ss + 1

  def rangeInitsFitCases (Phi : FMap) (layout : List Ident) :
      List (Literal × Block Op) → Bool
    | [] => true
    | (_, body) :: rest => rangeInitsFitStmts Phi layout body &&
        rangeInitsFitCases Phi layout rest
    termination_by cases => 2 * sizeOf cases + 1

  def rangeInitsFitDflt (Phi : FMap) (layout : List Ident) :
      Option (Block Op) → Bool
    | none => true
    | some body => rangeInitsFitStmts Phi layout body
    termination_by dflt => 2 * sizeOf dflt + 1
  decreasing_by
    all_goals simp_wf
end

mutual
  /-- Acyclic structured regions have a syntax-tree dominator structure: every
  nested block, conditional arm, and switch arm rejoins before the region
  exit.  Loops and non-local control remain separate proof cases. -/
  def shadowStraightStmt : Stmt Op → Bool
    | .block body | .cond _ body => shadowStraightStmts body
    | .switch _ cases dflt => shadowStraightCases cases &&
        shadowStraightDflt dflt
    | .letDecl _ _ | .assign _ _ | .exprStmt _ => true
    | .funDef _ _ _ _ | .forLoop _ _ _ _ |
      .break | .continue | .leave => false
    termination_by s => 2 * sizeOf s

  def shadowStraightStmts : Block Op → Bool
    | [] => true
    | s :: rest => shadowStraightStmt s && shadowStraightStmts rest
    termination_by ss => 2 * sizeOf ss + 1

  def shadowStraightCases : List (Literal × Block Op) → Bool
    | [] => true
    | (_, body) :: rest => shadowStraightStmts body &&
        shadowStraightCases rest
    termination_by cases => 2 * sizeOf cases + 1

  def shadowStraightDflt : Option (Block Op) → Bool
    | none => true
    | some body => shadowStraightStmts body
    termination_by dflt => 2 * sizeOf dflt + 1
  decreasing_by
    all_goals simp_wf
end

/-! ### Read-only ranges across one structured loop

`break` and `continue` are consumed by their owning loop.  A loop whose
initializer/post are straight-line regions and whose body is acyclic apart
from those two edges therefore returns only normally or by halting (provided
there is no `leave`).  A stable entry value can be shadowed around that whole
loop and copied back on normal exit; no edge-specific SSA copy is needed. -/

mutual
  def loopBodySafeStmt : Stmt Op → Bool
    | .block body | .cond _ body => loopBodySafeStmts body
    | .switch _ cases dflt => loopBodySafeCases cases && loopBodySafeDflt dflt
    | .letDecl _ _ | .assign _ _ | .exprStmt _ | .break | .continue => true
    | .funDef _ _ _ _ | .forLoop _ _ _ _ | .leave => false
    termination_by s => 2 * sizeOf s

  def loopBodySafeStmts : Block Op → Bool
    | [] => true
    | s :: rest => loopBodySafeStmt s && loopBodySafeStmts rest
    termination_by ss => 2 * sizeOf ss + 1

  def loopBodySafeCases : List (Literal × Block Op) → Bool
    | [] => true
    | (_, body) :: rest => loopBodySafeStmts body && loopBodySafeCases rest
    termination_by cases => 2 * sizeOf cases + 1

  def loopBodySafeDflt : Option (Block Op) → Bool
    | none => true
    | some body => loopBodySafeStmts body
    termination_by dflt => 2 * sizeOf dflt + 1
  decreasing_by
    all_goals simp_wf
end

def readOnlyLoopSafe : Stmt Op → Bool
  | .forLoop init _ post body =>
      shadowStraightStmts init && shadowStraightStmts post &&
        loopBodySafeStmts body
  | _ => false

def shadowReadOnlyLoopCandidate (P : String) (Phi : FMap)
    (layout : List Ident) (loop : Stmt Op) : List Ident → Option (Stmt Op)
  | [] => none
  | x :: xs =>
      match layout.findIdx? (fun y => y = x) with
      | none => shadowReadOnlyLoopCandidate P Phi layout loop xs
      | some idx =>
          let shadow := s!"{P}loop"
          if idx < 16 && x != shadow && !layout.contains shadow &&
              !stmtMentions shadow loop && !stmtDeclares x loop &&
              !stmtFunMentions x loop && !writesStmt x loop &&
              readOnlyLoopSafe loop then
            let renamed := renameStmt [(x, shadow)] loop
            if !(deepVarsStmt Phi [shadow] (shadow :: layout) renamed).contains shadow then
              some (.block [.letDecl [shadow] (some (.var x)),
                .block [renamed], .assign [x] (.var shadow)])
            else shadowReadOnlyLoopCandidate P Phi layout loop xs
          else shadowReadOnlyLoopCandidate P Phi layout loop xs

def shadowReadOnlyLoopHere (P : String) (Phi : FMap)
    (layout : List Ident) (loop : Stmt Op) : Option (Stmt Op) :=
  shadowReadOnlyLoopCandidate P Phi layout loop
    (deepVarsStmt Phi layout layout loop |>.filter fun x => !writesStmt x loop)

def readOnlyLoopLayoutAfter (layout : List Ident) : Stmt Op → List Ident
  | .letDecl xs _ => xs ++ layout
  | _ => layout

mutual
  def shadowOneReadOnlyLoopStmt (P : String) (Phi : FMap)
      (layout : List Ident) : Stmt Op → Option (Stmt Op)
    | loop@(.forLoop _ _ _ _) => shadowReadOnlyLoopHere P Phi layout loop
    | .block body => (.block ·) <$> shadowOneReadOnlyLoopStmts P Phi layout body
    | _ => none
    termination_by s => 2 * sizeOf s

  def shadowOneReadOnlyLoopStmts (P : String) (Phi : FMap)
      (layout : List Ident) : Block Op → Option (Block Op)
    | [] => none
    | s :: rest =>
        match shadowOneReadOnlyLoopStmt P Phi layout s with
        | some s' => some (s' :: rest)
        | none =>
            (s :: ·) <$> shadowOneReadOnlyLoopStmts P Phi
              (readOnlyLoopLayoutAfter layout s) rest
    termination_by ss => 2 * sizeOf ss + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def iterateReadOnlyLoopRangesFrom : Nat → FMap → List Ident →
    Block Op → Block Op
  | 0, _, _, body => body
  | n + 1, Phi, layout, body =>
      match freshPrefix (stmtsIdents body) with
      | none => body
      | some P =>
          match shadowOneReadOnlyLoopStmts P Phi layout body with
          | none => body
          | some body' => iterateReadOnlyLoopRangesFrom n Phi layout body'

def shadowStableCandidate (P : String) (Phi : FMap) (layout : List Ident)
    (body : Block Op) : List Ident → Option (Block Op)
  | [] => none
  | x :: xs =>
      match layout.findIdx? (fun y => y = x) with
      | some idx =>
          let written := writesStmts x body
          let shadow := s!"{P}r"
          if idx + 1 < 16 && x != shadow &&
              !layout.contains shadow && !stmtsMentions shadow body &&
              !stmtsDeclare x body && !hasDirectFun body && !hasLeaveStmts body &&
              !hasEscapingControlStmts body && !stmtsFunMention x body &&
              shadowStraightStmts body &&
              (!written || controlsBeforeWritesStmts [x] false body) then
            let renamed := renameStmts [(x, shadow)] body
            let copyBack := [.assign [x] (.var shadow)]
            let ranged := renamed
            let deep := deepVarsStmts Phi [shadow] (shadow :: layout) ranged
            if rangeInitsFitStmts Phi (shadow :: layout) ranged &&
                !deep.contains shadow then
              let init := some (.var x)
              some [.block ([.letDecl [shadow] init, .block ranged] ++ copyBack)]
            else shadowStableCandidate P Phi layout body xs
          else shadowStableCandidate P Phi layout body xs
      | none => shadowStableCandidate P Phi layout body xs

def shadowStableHere (P : String) (Phi : FMap) (layout : List Ident)
    (body : Block Op) : Option (Block Op) :=
  let deep := deepVarsStmts Phi layout layout body
  shadowStableCandidate P Phi layout body (deep.filter fun x => !writesStmts x body) <|>
    shadowStableCandidate P Phi layout body deep

/-- Prefer a writable deep value after stable live-range refinement.  This is
the complementary half of the split: the fresh slot becomes the reachable
assignment destination, while the surrounding region copies it back only
after its local stack frame has been discarded. -/
def shadowWrittenHere (P : String) (Phi : FMap) (layout : List Ident)
    (body : Block Op) : Option (Block Op) :=
  let deep := deepVarsStmts Phi layout layout body
  shadowStableCandidate P Phi layout body
    (deep.filter (fun x => writesStmts x body) |>.reverse)

def shadowGeneratedHere (P : String) (Phi : FMap) (layout : List Ident)
    (body : Block Op) : Option (Block Op) := do
  let x ← firstDeepStmts Phi layout layout body
  if !generatedRangeName x || writesStmts x body || hasDirectFun body then none else
  let idx ← layout.findIdx? (fun y => y = x)
  if 16 ≤ idx then none else
  let shadow := s!"{P}r"
  let renamed := renameStmts [(x, shadow)] body
  if (deepVarsStmts Phi [shadow] (shadow :: layout) renamed).contains shadow then
    none
  else some [.letDecl [shadow] (some (.var x)), .block renamed]

def shadowInsideExisting (P : String) (Phi : FMap) (layout : List Ident) :
    Block Op → Option (Block Op)
  | .block inner :: [] =>
      (fun inner' => [.block inner']) <$>
        shadowInsideExisting P Phi layout inner
  | s@(.letDecl [g] _) :: .block inner :: rest =>
      if generatedRangeName g then
        match shadowInsideExisting P Phi (g :: layout) inner with
        | some inner' => some (s :: .block inner' :: rest)
        | none => none
      else shadowStableHere P Phi layout (s :: .block inner :: rest)
  | body => shadowStableHere P Phi layout body
  termination_by body => sizeOf body
  decreasing_by
    all_goals simp_all
    all_goals omega

def shadowInsideExistingWritten (P : String) (Phi : FMap)
    (layout : List Ident) : Block Op → Option (Block Op)
  | .block inner :: [] =>
      (fun inner' => [.block inner']) <$>
        shadowInsideExistingWritten P Phi layout inner
  | s@(.letDecl [g] _) :: .block inner :: rest =>
      if generatedRangeName g then
        match shadowInsideExistingWritten P Phi (g :: layout) inner with
        | some inner' => some (s :: .block inner' :: rest)
        | none => none
      else shadowWrittenHere P Phi layout (s :: .block inner :: rest)
  | body => shadowWrittenHere P Phi layout body
  termination_by body => sizeOf body
  decreasing_by
    all_goals simp_all
    all_goals omega

def nestedRangeFunctionStmts (body : Block Op) : Block Op :=
  let (scope, _) := hoistInfos 0 body
  body.map fun s => match s with
    | .funDef f ps rs fnBody =>
        let fnBody' := match freshPrefix (stmtsIdents fnBody) with
          | some P => (shadowInsideExisting P [scope] (ps ++ rs) fnBody).getD fnBody
          | none => fnBody
        .funDef f ps rs fnBody'
    | other => other

def nestedWrittenRangeFunctionStmts (body : Block Op) : Block Op :=
  let (scope, _) := hoistInfos 0 body
  body.map fun s => match s with
    | .funDef f ps rs fnBody =>
        let fnBody' := match freshPrefix (stmtsIdents fnBody) with
          | some P =>
              (shadowInsideExistingWritten P [scope] (ps ++ rs) fnBody).getD fnBody
          | none => fnBody
        .funDef f ps rs fnBody'
    | other => other

def iterateNestedRangeFunctionStmts : Nat → Block Op → Block Op
  | 0, body => body
  | n + 1, body =>
      iterateNestedRangeFunctionStmts n (nestedRangeFunctionStmts body)

def shadowOneRegionStmts (P : String) (Phi : FMap) (layout : List Ident) :
    Block Op → Option (Block Op)
  | body => shadowStableHere P Phi layout body

def iterateRegionRanges : Nat → Block Op → Block Op
  | 0, body => body
  | n + 1, body =>
      match freshPrefix (stmtsIdents body) with
      | none => body
      | some P =>
          let (scope, _) := hoistInfos 0 body
          match shadowOneRegionStmts P [scope] [] body with
          | some body' => iterateRegionRanges n body'
          | none => body

def iterateRegionRangesFrom : Nat → FMap → List Ident → Block Op → Block Op
  | 0, _, _, body => body
  | n + 1, Phi, layout, body =>
      match freshPrefix (stmtsIdents body) with
      | none => body
      | some P =>
          match shadowOneRegionStmts P Phi layout body with
          | some body' => iterateRegionRangesFrom n Phi layout body'
          | none => body

def rangeFunctionStmts (fuel : Nat) (body : Block Op) : Block Op :=
  let (scope, _) := hoistInfos 0 body
  body.map fun s => match s with
    | .funDef f ps rs fnBody =>
        .funDef f ps rs (iterateRegionRangesFrom fuel [scope] (ps ++ rs) fnBody)
    | other => other

def directDecls : Block Op → List Ident
  | [] => []
  | .letDecl xs _ :: rest => xs ++ directDecls rest
  | _ :: rest => directDecls rest

def deadPrefixSearch : Block Op → Block Op → Option (Block Op)
  | _, [] => none
  | pre, s :: rest =>
      let pre' := pre ++ [s]
      let names := directDecls pre'
      if !rest.isEmpty && !names.isEmpty && names.Nodup &&
          names.all (fun x => !stmtsMentions x rest) && !hasDirectFun pre' then
        some (.block pre' :: rest)
      else deadPrefixSearch pre' rest
  termination_by _ rest => rest.length

def scopeDeadPrefixHere (body : Block Op) : Option (Block Op) :=
  deadPrefixSearch [] body

mutual
  def scopeOneDeadPrefixStmt : Stmt Op → Option (Stmt Op)
    | .block body => (.block ·) <$> scopeOneDeadPrefixStmts body
    | .funDef f ps rs body => (.funDef f ps rs ·) <$> scopeOneDeadPrefixStmts body
    | .cond c body => (.cond c ·) <$> scopeOneDeadPrefixStmts body
    | .switch c cases dflt =>
        match scopeOneDeadPrefixCases cases with
        | some cases' => some (.switch c cases' dflt)
        | none =>
            match dflt with
            | some body => (.switch c cases ∘ some) <$> scopeOneDeadPrefixStmts body
            | none => none
    | .forLoop init c post body =>
        match scopeOneDeadPrefixStmts post with
        | some post' => some (.forLoop init c post' body)
        | none =>
            (.forLoop init c post ·) <$> scopeOneDeadPrefixStmts body
    | _ => none
    termination_by s => 2 * sizeOf s

  def scopeOneDeadPrefixStmts : Block Op → Option (Block Op)
    | [] => none
    | ss@(s :: rest) =>
        match scopeDeadPrefixHere ss with
        | some ss' => some ss'
        | none =>
            match scopeOneDeadPrefixStmt s with
            | some s' => some (s' :: rest)
            | none => (s :: ·) <$> scopeOneDeadPrefixStmts rest
    termination_by ss => 2 * sizeOf ss + 1

  def scopeOneDeadPrefixCases :
      List (Literal × Block Op) → Option (List (Literal × Block Op))
    | [] => none
    | (l, body) :: rest =>
        match scopeOneDeadPrefixStmts body with
        | some body' => some ((l, body') :: rest)
        | none => ((l, body) :: ·) <$> scopeOneDeadPrefixCases rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def iterateDeadPrefixes : Nat → Block Op → Block Op
  | 0, body => body
  | n + 1, body =>
      match scopeOneDeadPrefixStmts body with
      | some body' => iterateDeadPrefixes n body'
      | none => body

def iterateDeadPrefixesHere : Nat → Block Op → Block Op
  | 0, body => body
  | n + 1, body =>
      match scopeDeadPrefixHere body with
      | some body' => iterateDeadPrefixesHere n body'
      | none => body

mutual
  def scopeDeadPrefixesStmt : Nat → Stmt Op → Stmt Op
    | 0, s => s
    | n + 1, .block body => .block (scopeDeadPrefixesStmts n body)
    | n + 1, .funDef f ps rs body =>
        .funDef f ps rs (scopeDeadPrefixesStmts n body)
    | n + 1, .cond c body => .cond c (scopeDeadPrefixesStmts n body)
    | n + 1, .switch c cases dflt => .switch c
        (scopeDeadPrefixesCases n cases) (scopeDeadPrefixesDflt n dflt)
    | n + 1, .forLoop init c post body => .forLoop
        init c (scopeDeadPrefixesStmts n post)
        (scopeDeadPrefixesStmts n body)
    | _, s => s

  def scopeDeadPrefixesStmts : Nat → Block Op → Block Op
    | 0, body => body
    | n + 1, body =>
        let split := iterateDeadPrefixes 64 body
        split.map (scopeDeadPrefixesStmt n)

  def scopeDeadPrefixesCases : Nat →
      List (Literal × Block Op) → List (Literal × Block Op)
    | 0, cases => cases
    | _n + 1, [] => []
    | n + 1, (l, body) :: rest =>
        (l, scopeDeadPrefixesStmts n body) :: scopeDeadPrefixesCases n rest

  def scopeDeadPrefixesDflt : Nat → Option (Block Op) → Option (Block Op)
    | 0, dflt => dflt
    | _n + 1, none => none
    | n + 1, some body => some (scopeDeadPrefixesStmts n body)
end

def scopeDeadFunctionStmt : Stmt Op → Stmt Op
  | .funDef f ps rs body =>
      .funDef f ps rs (scopeDeadPrefixesStmts 64 body)
  | s => s

def scopeDeadFunctionStmts (body : Block Op) : Block Op :=
  body.map scopeDeadFunctionStmt

def iterateAliasesFrom : Nat → List Ident → Block Op → Block Op
  | 0, _, body => body
  | n + 1, layout, body =>
      match aliasOneStmts layout body with
      | some body' => iterateAliasesFrom n layout body'
      | none => body

def aliasFunctionStmt : Stmt Op → Stmt Op
  | .funDef f ps rs body =>
      .funDef f ps rs (iterateAliasesFrom 4096 (ps ++ rs) body)
  | s => s

def aliasFunctionStmts (body : Block Op) : Block Op :=
  body.map aliasFunctionStmt

/-- Seed copy propagation with identity facts for function parameters and
returns.  Besides being tautological, these facts let the existing verified
propagator refresh an entry after `x := y`, which is exactly the copy pattern
introduced by range splitting and slot reuse. -/
def identityPEnv (bound : List Ident) : PEnv :=
  bound.map fun x => (x, .var x)

def iterateSeededProp : Nat → List Ident → Block Op → Block Op
  | 0, _, body => body
  | n + 1, bound, body =>
      iterateSeededProp n bound (propStmts true (identityPEnv bound) body).1

def propagateFunctionStmt : Stmt Op → Stmt Op
  | .funDef f ps rs body =>
      .funDef f ps rs (iterateSeededProp 64 (ps ++ rs) body)
  | s => s

def propagateFunctionStmts (body : Block Op) : Block Op :=
  body.map propagateFunctionStmt

end StackV2

def legacyStackLayoutBlock (b : Block Op) : Block Op :=
  iterateTailScope 1024 (iterateStackLayout 1024 (scheduleStmts b))

def aggressiveStackLayoutBlock (b : Block Op) : Block Op :=
  let copied := iterateCopyBack 1024 (scheduleStmts b)
  let prefixed := copied
  let scopedEarly := StackV2.scopeDeadFunctionStmts prefixed
  let tailed := iterateTailScope 4096 scopedEarly
  let reused := iterateStackLayout 4096 tailed
  let staged := reused
  let ranged := iterateStackLayout 4096 (StackV2.rangeFunctionStmts 64 staged)
  let rangedReused := StackV2.rangeFunctionStmts 64 (iterateStackLayout 4096 ranged)
  let aliased := StackV2.aliasFunctionStmts rangedReused
  let rangedFinal := StackV2.rangeFunctionStmts 64 aliased
  let nestedStable := StackV2.iterateNestedRangeFunctionStmts 1 rangedFinal
  let nested := StackV2.nestedWrittenRangeFunctionStmts nestedStable
  let nestedReused := iterateStackLayout 4096 nested
  let nestedAliased := StackV2.aliasFunctionStmts nestedReused
  stageCallsBlock (StackV2.scopeDeadFunctionStmts nestedAliased)

/-- Run the aggressive fixed point inside one function frame.  Unlike the
whole-block driver, every search starts at the function's parameter/result
layout and receives the already-hoisted enclosing signature scope. -/
def aggressiveStackLayoutFunction (Phi : FMap) (layout : List Ident)
    (body : Block Op) : Block Op :=
  let copied := iterateCopyBackFrom 1024 layout (scheduleStmts body)
  let scopedEarly := StackV2.scopeDeadPrefixesStmts 64 copied
  let tailed := iterateTailScopeFrom 4096 layout scopedEarly
  let reused := iterateStackLayoutFrom 4096 layout tailed
  let loopRanged := StackV2.iterateReadOnlyLoopRangesFrom 16 Phi layout reused
  let ranged := StackV2.iterateRegionRangesFrom 64 Phi layout loopRanged
  let rangedReused := StackV2.iterateRegionRangesFrom 64 Phi layout
    (iterateStackLayoutFrom 4096 layout ranged)
  let aliased := StackV2.iterateAliasesFrom 4096 layout rangedReused
  let rangedFinal := StackV2.iterateRegionRangesFrom 64 Phi layout aliased
  let nestedStable := match freshPrefix (stmtsIdents rangedFinal) with
    | some P => (StackV2.shadowInsideExisting P Phi layout rangedFinal).getD rangedFinal
    | none => rangedFinal
  let nested := match freshPrefix (stmtsIdents nestedStable) with
    | some P =>
        (StackV2.shadowInsideExistingWritten P Phi layout nestedStable).getD nestedStable
    | none => nestedStable
  let nestedReused := iterateStackLayoutFrom 4096 layout nested
  let nestedAliased := StackV2.iterateAliasesFrom 4096 layout nestedReused
  let scopedFinal := StackV2.scopeDeadPrefixesStmts 64 nestedAliased
  match freshPrefix (stmtsIdents scopedFinal) with
  | some P => iterateStageWithLayout 16384 P Phi layout scopedFinal
  | none => scopedFinal

/-- The aggressive fallback deliberately performs repeated whole-function
data-flow scans.  Keep that search bounded on generated integration IR using
both an object-wide identifier-occurrence budget and a tighter per-function
budget.  Above either bound the legacy pass still gives the established fast
rejection, while moderate functions (including PoolLiquidity and SwapMath) get
the full dominance/liveness refinement.  This is a compile-time resource bound,
not a semantic restriction: both alternatives are independently proved
equivalent. -/
def aggressiveStackLayoutBudget : Nat := 8192

def aggressiveFunctionLayoutBudget : Nat := 8192

def directFunctionsWithinAggressiveBudget : Block Op → Bool
  | [] => true
  | .funDef _ _ _ body :: rest =>
      (stmtsIdents body).length ≤ aggressiveFunctionLayoutBudget &&
        directFunctionsWithinAggressiveBudget rest
  | _ :: rest => directFunctionsWithinAggressiveBudget rest

def withinAggressiveStackLayoutBudget (b : Block Op) : Bool :=
  (stmtsIdents b).length ≤ aggressiveStackLayoutBudget &&
    directFunctionsWithinAggressiveBudget b

/-- Transform each function independently so an oversized sibling neither
suppresses nor slows layout of a moderate function.  The shared scope is used
only for call signatures; function bodies remain separate fixed points. -/
def scopedAggressiveFunctions (scope : FScopeInfo) : Block Op → Block Op
  | [] => []
  | .funDef f ps rs body :: rest =>
      let body' :=
        if (stmtsIdents body).length ≤ aggressiveFunctionLayoutBudget then
          aggressiveStackLayoutFunction [scope] (ps ++ rs) body
        else body
      .funDef f ps rs body' :: scopedAggressiveFunctions scope rest
  | s :: rest => s :: scopedAggressiveFunctions scope rest

def scopedAggressiveStackLayoutBlock (b : Block Op) : Block Op :=
  let (scope, _) := hoistInfos 0 b
  scopedAggressiveFunctions scope b

/-- Preserve the established layout and bytecode whenever it already compiles;
use the more aggressive dominance-local pipeline only as a stack-pressure
fallback on bounded functions. This keeps the new acceptance frontier from
perturbing gas for the previously supported fragment and prevents generated
multi-megabyte functions from turning a known rejection into an unbounded
compile-time search. -/
def stackLayoutBlock (b : Block Op) : Block Op :=
  let legacy := legacyStackLayoutBlock b
  if (compile legacy).isSome then legacy
  else
    let localized := scopedAggressiveStackLayoutBlock b
    if (compile localized).isSome then localized
    else if withinAggressiveStackLayoutBudget b then aggressiveStackLayoutBlock b
    else localized

mutual
  /-- Apply stack layout independently to every code block in an object tree. -/
  def stackLayoutObject : Object Op → Object Op
    | .mk name code subs segs =>
        .mk name (stackLayoutBlock code) (stackLayoutObjects subs) segs

  def stackLayoutObjects : List (Object Op) → List (Object Op)
    | [] => []
    | o :: os => stackLayoutObject o :: stackLayoutObjects os
end

end YulEvmCompiler.Optimizer
