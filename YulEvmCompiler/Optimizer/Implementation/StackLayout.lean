import YulEvmCompiler.Optimizer.Implementation.Frame
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

def iterateTailScope : Nat → Block Op → Block Op
  | 0, b => b
  | n + 1, b =>
      match scopeOneStmts [] b with
      | some b' => iterateTailScope n b'
      | none => b

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

def iterateStackLayout : Nat → Block Op → Block Op
  | 0, b => b
  | n + 1, b =>
      match reuseOneStmts [] [] b with
      | some b' => iterateStackLayout n b'
      | none => b

def stackLayoutBlock (b : Block Op) : Block Op :=
  iterateTailScope 1024 (iterateStackLayout 1024 (scheduleStmts b))

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
