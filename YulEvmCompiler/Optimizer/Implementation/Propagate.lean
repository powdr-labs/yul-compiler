import YulEvmCompiler.Optimizer.Spec.Pass
import YulEvmCompiler.Optimizer.Implementation.Simplify
import YulEvmCompiler.Optimizer.Implementation.Frame
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.Propagate

**Constant + copy propagation, binding-preserving.** A forward walk carries an
environment `σ` of *known bindings*: after `let x := 5`, later reads of `x`
(until invalidated) are replaced by `5`; after `let y := x`, reads of `y` become
`x`; `let x` (uninitialized) yields `x ↦ 0` (Yul zero-initializes); and an
assignment `x := <literal>` with `x` already tracked *refreshes* the entry —
σ-membership proves `x` is bound, so `VEnv.set` really updates. A fold-at-rhs
step (reusing `pureFold`) collapses literal chains (`let a := 1  let b :=
add(a, 1)` → `let b := 2`) in a single traversal.

Bindings are **never removed** — that is exactly what makes the pass sound in
the pointwise `EquivBlock` spec (where binding *removal* is unsound: it changes
stuckness on ill-scoped environments). Here, the kept `let` guarantees the
variable is bound to the known value in every execution that reaches a use
site, on *both* sides of the rewrite, so values, states, environments, and
outcomes are preserved in both directions with no well-scopedness assumption.

## Invalidation (syntactic, conservative)

An entry `(x, rhs)` dies when `x` is re-declared or assigned, or (for a copy
entry `y ↦ x`) when its *source* `x` is re-declared or assigned. Nested
constructs invalidate through their write sets (`writeSetStmts` — every ident
let-declared or assigned at any depth, *not* descending into `funDef` bodies,
whose fresh callee environments cannot touch caller variables). A `for` loop
rewrites its condition/post/body under a σ pruned by the loop's whole write
set, making the loop environment invariant *by construction*. `funDef` bodies
restart at `σ = []`.

## The proof design: a relation, not just the function

Soundness is proven for an inductive relation `PropRel σ σ' code code'`
("`code'` is a valid σ-propagation of `code`") with *skip alternatives* for
every action and *mandatory* pruning, and `propStmts` is proven to inhabit it.
The semantic theorem (`prop_fwd`/`prop_bwd`) is one bidirectional `Step`
simulation over the relation, carrying the invariant `Compat V σ` (each entry's
key is bound and agrees with its right-hand side). Function environments are
related by the syntactic `PFunsRel` (equal signatures, `PropRel []`-related
bodies), so the `call` cases recurse directly on the callee-body sub-derivation
— no size induction and no semantic function-environment relation is needed.

The relational formulation is what the **object path** needs: layout resolution
creates number literals from `dataoffset`/`datasize` calls, so the *function*
does more work on resolved code and no syntactic commutation with resolution
exists. The relation's skip rules absorb exactly that mismatch:
`PropRel` is closed under `resolveForLayoutStmts` by a purely syntactic
induction (see `PropagateResolve.lean`), giving the full pass on object code
blocks with no `litOK`-style weakening.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Known-binding environments -/

/-- The right-hand side of a known binding: a number literal or another
variable. String and bool literals are deliberately excluded (strings interact
with `dataoffset`/`datasize` resolution; bools add nothing solc emits). -/
inductive PRhs
  | lit (n : Nat)
  | var (x : Ident)
  deriving Repr, DecidableEq, Inhabited

/-- A known-binding environment: an association list, most recent first. -/
abbrev PEnv := List (Ident × PRhs)

/-- The expression a known binding stands for. -/
def PRhs.toExpr : PRhs → Expr Op
  | .lit n => .lit (.number n)
  | .var x => .var x

/-- Look up the tracked binding of `x`, if any. -/
def lookupEnv (σ : PEnv) (x : Ident) : Option PRhs :=
  (σ.find? (fun p => p.1 = x)).map (·.2)

/-- Classify an expression as a trackable right-hand side. -/
def classify : Expr Op → Option PRhs
  | .lit (.number n) => some (.lit n)
  | .var x => some (.var x)
  | _ => none

/-- Does the entry mention (as key or as copy-source) an ident from `ws`? -/
def entryHits (ws : List Ident) : Ident × PRhs → Bool
  | (x, .lit _) => ws.contains x
  | (x, .var y) => ws.contains x || ws.contains y

/-- Drop every entry whose key or copy-source is written by `ws`. -/
def prune (σ : PEnv) (ws : List Ident) : PEnv :=
  σ.filter (fun p => !entryHits ws p)

/-! ### Write sets

Every ident let-declared or assigned at any depth — `funDef` bodies excluded
(their fresh callee environments cannot touch caller variables). Conservative:
shadowing is not tracked. -/

mutual

/-- Idents a statement may write (declare or assign), at any depth. -/
def writeSetStmt : Stmt Op → List Ident
  | .block body => writeSetStmts body
  | .funDef _ _ _ _ => []
  | .letDecl xs _ => xs
  | .assign xs _ => xs
  | .cond _ body => writeSetStmts body
  | .switch _ cases dflt => writeSetCases cases ++ writeSetDflt dflt
  | .forLoop init _ post body =>
      writeSetStmts init ++ writeSetStmts post ++ writeSetStmts body
  | .exprStmt _ => []
  | .break => []
  | .continue => []
  | .leave => []

/-- Idents a statement sequence may write. -/
def writeSetStmts : List (Stmt Op) → List Ident
  | [] => []
  | s :: rest => writeSetStmt s ++ writeSetStmts rest

/-- Idents any `switch` case body may write. -/
def writeSetCases : List (Literal × Block Op) → List Ident
  | [] => []
  | (_, b) :: rest => writeSetStmts b ++ writeSetCases rest

/-- Idents a `switch` default may write. -/
def writeSetDflt : Option (Block Op) → List Ident
  | none => []
  | some b => writeSetStmts b

end

/-! ### Substitution and rhs folding -/

mutual

/-- Replace reads of tracked variables by their known right-hand sides. -/
def substExpr (σ : PEnv) : Expr Op → Expr Op
  | .lit l => .lit l
  | .var x =>
      match lookupEnv σ x with
      | some r => r.toExpr
      | none => .var x
  | .builtin op args => .builtin op (substArgs σ args)
  | .call f args => .call f (substArgs σ args)

/-- Substitute each expression of an argument list. -/
def substArgs (σ : PEnv) : List (Expr Op) → List (Expr Op)
  | [] => []
  | e :: rest => substExpr σ e :: substArgs σ rest

end

/-- Fold a pure builtin on all-literal arguments to its literal (else identity). -/
def foldRhs : Expr Op → Expr Op
  | .lit l => .lit l
  | .var x => .var x
  | .call f args => .call f args
  | .builtin op args =>
      match asLits args with
      | some lits =>
          match pureFold op lits with
          | some l => .lit l
          | none => .builtin op args
      | none => .builtin op args

/-- The production right-hand-side rewrite: substitute, then fold. -/
def rhsExpr (σ : PEnv) (e : Expr Op) : Expr Op := foldRhs (substExpr σ e)

/-! ### The transform -/

/-- The copy-fact depth gate's live-local budget. Substituting a copy
(`y ↦ x`) replaces a read of a recently bound (stack-shallow) variable with a
read of an older (deeper) one, and the backend's variable reads are `DUP`s
hard-limited at depth 16 (`compileExpr`: `off + idx < 16`). Copy facts are
therefore created only inside scopes whose maximum simultaneously-live local
count (`liveMaxStmts`, shared with the `InlineCalls` guard) stays within this
budget — small inlined-helper frames qualify; solc's big `dispatch_*`
dispatcher frames do not (they stopped compiling when copies were substituted
ungated). Constant entries can only relieve depth (a literal is a `PUSH`)
and are always created. A wrong gate costs optimization (the compile
fallback), never coverage or soundness. -/
def copyDepthLimit : Nat := 12

/-- Enable copy facts for a scope entered with `acc` already-live bindings? -/
def copyGate (acc : Nat) (body : Block Op) : Bool :=
  decide (liveMaxStmts acc body ≤ copyDepthLimit)

/-- Production classification: number literals always; copy entries (`y ↦ x`)
only when the enclosing scope passed the depth gate (see `copyGate`). Both
are refinements of the relation's `classify`, so any gate policy is sound —
and because the resolution congruence transports the frozen relation
instance, the policy needs no resolution stability. -/
def classifyProd : Bool → Expr Op → Option PRhs
  | _, .lit (.number n) => some (.lit n)
  | true, .var x => some (.var x)
  | _, _ => none

/-- Production classification refines the relation's classification. -/
theorem classifyProd_sub {copyOK : Bool} {e : Expr Op} {r : PRhs}
    (h : classifyProd copyOK e = some r) :
    classify e = some r := by
  unfold classifyProd at h
  split at h <;> simp_all [classify]

/-- The tracked environment after `let xs := rhs'`: prune the shadowed names,
then track a singleton whose rewritten rhs is classifiable. -/
def letEnv (copyOK : Bool) (σ : PEnv) (xs : List Ident) (rhs' : Expr Op) : PEnv :=
  match xs, classifyProd copyOK rhs' with
  | [x], some r => (x, r) :: prune σ [x]
  | _, _ => prune σ xs

/-- The tracked environment after `let xs` (zero-initialized): prune, and track
a singleton as `0`. -/
def letZeroEnv (σ : PEnv) (xs : List Ident) : PEnv :=
  match xs with
  | [x] => (x, .lit 0) :: prune σ [x]
  | _ => prune σ xs

/-- The tracked environment after `xs := rhs'`: prune, except a singleton
assignment to an *already-tracked* variable (hence provably bound) with a
classifiable rhs *refreshes* the entry. -/
def assignEnv (copyOK : Bool) (σ : PEnv) (xs : List Ident) (rhs' : Expr Op) : PEnv :=
  match xs, classifyProd copyOK rhs' with
  | [x], some r =>
      if (lookupEnv σ x).isSome then (x, r) :: prune σ [x] else prune σ xs
  | _, _ => prune σ xs

mutual

/-- Propagate through one statement, returning the rewritten statement and the
tracked environment for the statements that follow it. -/
def propStmt (copyOK : Bool) (σ : PEnv) : Stmt Op → Stmt Op × PEnv
  | .block body =>
      (.block (propStmts copyOK σ body).1, prune σ (writeSetStmts body))
  | .funDef n ps rs body =>
      (.funDef n ps rs
        (propStmts (copyGate (ps.length + rs.length) body) [] body).1, σ)
  | .letDecl xs none =>
      (.letDecl xs none, letZeroEnv σ xs)
  | .letDecl xs (some e) =>
      let r := rhsExpr σ e
      (.letDecl xs (some r), letEnv copyOK σ xs r)
  | .assign xs e =>
      let r := rhsExpr σ e
      (.assign xs r, assignEnv copyOK σ xs r)
  | .cond c body =>
      (.cond (substExpr σ c) (propStmts copyOK σ body).1, prune σ (writeSetStmts body))
  | .switch c cases dflt =>
      (.switch (substExpr σ c) (propCases copyOK σ cases) (propDflt copyOK σ dflt),
        prune σ (writeSetCases cases ++ writeSetDflt dflt))
  | .forLoop init c post body =>
      let pinit := propStmts copyOK σ init
      let σL := prune pinit.2 (writeSetStmts post ++ writeSetStmts body)
      (.forLoop pinit.1 (substExpr σL c) (propStmts copyOK σL post).1
        (propStmts copyOK σL body).1,
        prune σ (writeSetStmts init ++ writeSetStmts post ++ writeSetStmts body))
  | .exprStmt e => (.exprStmt (substExpr σ e), σ)
  | .break => (.break, σ)
  | .continue => (.continue, σ)
  | .leave => (.leave, σ)

/-- Propagate through a statement sequence, threading the environment. -/
def propStmts (copyOK : Bool) (σ : PEnv) : List (Stmt Op) → List (Stmt Op) × PEnv
  | [] => ([], σ)
  | s :: rest =>
      let ps := propStmt copyOK σ s
      let prest := propStmts copyOK ps.2 rest
      (ps.1 :: prest.1, prest.2)

/-- Propagate through each `switch` case body (labels preserved). -/
def propCases (copyOK : Bool) (σ : PEnv) :
    List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, (propStmts copyOK σ b).1) :: propCases copyOK σ rest

/-- Propagate through a `switch`'s optional default. -/
def propDflt (copyOK : Bool) (σ : PEnv) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some ((propStmts copyOK σ b).1)

end

/-- The pass entry point: propagate through a top-level block. -/
def propagateBlock (b : Block Op) : Block Op := (propStmts (copyGate 0 b) [] b).1

/-! ### The propagation relation

Soundness is proven for a *relation* with skip alternatives for every action
(and mandatory pruning), which the deterministic transform inhabits. The skip
rules are load-bearing for the object path: layout resolution creates number
literals from `dataoffset`/`datasize` calls, so on resolved code the *function*
would act at more sites; the relation absorbs the mismatch, making it closed
under resolution by a purely syntactic induction. -/

/-- The syntactic classes the relation ranges over: the five `Code` classes
plus `switch` case lists and defaults (encoded as one indexed inductive for the
same reason `Step` is — mutual predicate induction is not ergonomic). -/
inductive PCode (Op : Type)
  | expr (e : Expr Op)
  | args (es : List (Expr Op))
  | stmt (s : Stmt Op)
  | stmts (ss : List (Stmt Op))
  | loop (c : Expr Op) (post body : Block Op)
  | cases (cs : List (Literal × Block Op))
  | odflt (d : Option (Block Op))

/-- Valid rewritten right-hand sides: substituted, optionally folded. -/
inductive RhsRel (σ : PEnv) (e : Expr Op) : Expr Op → Prop
  | subst : RhsRel σ e (substExpr σ e)
  | fold : RhsRel σ e (rhsExpr σ e)

/-- Valid tracked environments after `let xs := rhs'` (creation optional). -/
inductive LetEnvRel (σ : PEnv) (xs : List Ident) (rhs' : Expr Op) : PEnv → Prop
  | skip : LetEnvRel σ xs rhs' (prune σ xs)
  | create {x r} : xs = [x] → classify rhs' = some r →
      LetEnvRel σ xs rhs' ((x, r) :: prune σ [x])

/-- Valid tracked environments after `let xs` (zero-tracking optional). -/
inductive LetZeroEnvRel (σ : PEnv) (xs : List Ident) : PEnv → Prop
  | skip : LetZeroEnvRel σ xs (prune σ xs)
  | zero {x} : xs = [x] → LetZeroEnvRel σ xs ((x, .lit 0) :: prune σ [x])

/-- Valid tracked environments after `xs := rhs'`: prune, or *refresh* a
singleton assignment to an already-tracked (hence provably bound) target. The
refresh also prunes copy entries sourced at the target — a surviving `y ↦ x`
would read the new value of `x`. -/
inductive AssignEnvRel (σ : PEnv) (xs : List Ident) (rhs' : Expr Op) : PEnv → Prop
  | skip : AssignEnvRel σ xs rhs' (prune σ xs)
  | refresh {x r} : xs = [x] → (lookupEnv σ x).isSome → classify rhs' = some r →
      AssignEnvRel σ xs rhs' ((x, r) :: prune σ [x])

/-- `PropRel σ σ' pc pc'`: `pc'` is a valid `σ`-propagation of `pc`, leaving
`σ'` for what follows. Constructor-preserving on statements; every action has a
skip alternative (via the `RhsRel`/`*EnvRel` premises); pruning is mandatory. -/
inductive PropRel : PEnv → PEnv → PCode Op → PCode Op → Prop
  | expr {σ : PEnv} {e e' : Expr Op} :
      RhsRel σ e e' →
      PropRel σ σ (.expr e) (.expr e')
  | args {σ : PEnv} {es : List (Expr Op)} :
      PropRel σ σ (.args es) (.args (substArgs σ es))
  | blockS {σ σb : PEnv} {body body' : Block Op} :
      PropRel σ σb (.stmts body) (.stmts body') →
      PropRel σ (prune σ (writeSetStmts body)) (.stmt (.block body)) (.stmt (.block body'))
  | funDefS {σ σb : PEnv} {n : Ident} {ps rs : List Ident} {body body' : Block Op} :
      PropRel [] σb (.stmts body) (.stmts body') →
      PropRel σ σ (.stmt (.funDef n ps rs body)) (.stmt (.funDef n ps rs body'))
  | letSomeS {σ σ2 : PEnv} {xs : List Ident} {e rhs' : Expr Op} :
      RhsRel σ e rhs' → LetEnvRel σ xs rhs' σ2 →
      PropRel σ σ2 (.stmt (.letDecl xs (some e))) (.stmt (.letDecl xs (some rhs')))
  | letNoneS {σ σ2 : PEnv} {xs : List Ident} :
      LetZeroEnvRel σ xs σ2 →
      PropRel σ σ2 (.stmt (.letDecl xs none)) (.stmt (.letDecl xs none))
  | assignS {σ σ2 : PEnv} {xs : List Ident} {e rhs' : Expr Op} :
      RhsRel σ e rhs' → AssignEnvRel σ xs rhs' σ2 →
      PropRel σ σ2 (.stmt (.assign xs e)) (.stmt (.assign xs rhs'))
  | condS {σ σb : PEnv} {c : Expr Op} {body body' : Block Op} :
      PropRel σ σb (.stmts body) (.stmts body') →
      PropRel σ (prune σ (writeSetStmts body)) (.stmt (.cond c body))
        (.stmt (.cond (substExpr σ c) body'))
  | switchS {σ : PEnv} {c : Expr Op} {cases cases' : List (Literal × Block Op)}
      {dflt dflt' : Option (Block Op)} :
      PropRel σ σ (.cases cases) (.cases cases') →
      PropRel σ σ (.odflt dflt) (.odflt dflt') →
      PropRel σ (prune σ (writeSetCases cases ++ writeSetDflt dflt))
        (.stmt (.switch c cases dflt))
        (.stmt (.switch (substExpr σ c) cases' dflt'))
  | forS {σ σi σp σb σL : PEnv} {init init' : Block Op} {c : Expr Op}
      {post post' body body' : Block Op} :
      PropRel σ σi (.stmts init) (.stmts init') →
      σL = prune σi (writeSetStmts post ++ writeSetStmts body) →
      PropRel σL σp (.stmts post) (.stmts post') →
      PropRel σL σb (.stmts body) (.stmts body') →
      PropRel σ (prune σ (writeSetStmts init ++ writeSetStmts post ++ writeSetStmts body))
        (.stmt (.forLoop init c post body))
        (.stmt (.forLoop init' (substExpr σL c) post' body'))
  | exprStmtS {σ : PEnv} {e : Expr Op} :
      PropRel σ σ (.stmt (.exprStmt e)) (.stmt (.exprStmt (substExpr σ e)))
  | breakS {σ : PEnv} : PropRel σ σ (.stmt .break) (.stmt .break)
  | continueS {σ : PEnv} : PropRel σ σ (.stmt .continue) (.stmt .continue)
  | leaveS {σ : PEnv} : PropRel σ σ (.stmt .leave) (.stmt .leave)
  | nilSS {σ : PEnv} : PropRel σ σ (.stmts []) (.stmts [])
  | consSS {σ σ1 σ' : PEnv} {s s' : Stmt Op} {rest rest' : List (Stmt Op)} :
      PropRel σ σ1 (.stmt s) (.stmt s') → PropRel σ1 σ' (.stmts rest) (.stmts rest') →
      PropRel σ σ' (.stmts (s :: rest)) (.stmts (s' :: rest'))
  | loopL {σ σp σb : PEnv} {c : Expr Op} {post body post' body' : Block Op} :
      prune σ (writeSetStmts post ++ writeSetStmts body) = σ →
      PropRel σ σp (.stmts post) (.stmts post') →
      PropRel σ σb (.stmts body) (.stmts body') →
      PropRel σ σ (.loop c post body) (.loop (substExpr σ c) post' body')
  | casesNil {σ : PEnv} : PropRel σ σ (.cases []) (.cases [])
  | casesCons {σ σb : PEnv} {l : Literal} {b b' : Block Op}
      {rest rest' : List (Literal × Block Op)} :
      PropRel σ σb (.stmts b) (.stmts b') → PropRel σ σ (.cases rest) (.cases rest') →
      PropRel σ σ (.cases ((l, b) :: rest)) (.cases ((l, b') :: rest'))
  | odfltNone {σ : PEnv} : PropRel σ σ (.odflt none) (.odflt none)
  | odfltSome {σ σb : PEnv} {b b' : Block Op} :
      PropRel σ σb (.stmts b) (.stmts b') →
      PropRel σ σ (.odflt (some b)) (.odflt (some b'))

/-! ### The transform inhabits the relation -/

/-- `letEnv` is a valid `LetEnvRel` choice — for any gate policy. -/
theorem letEnv_rel (copyOK : Bool) (σ : PEnv) (xs : List Ident) (rhs' : Expr Op) :
    LetEnvRel σ xs rhs' (letEnv copyOK σ xs rhs') := by
  unfold letEnv
  split
  · next x r hcl => exact .create rfl (classifyProd_sub hcl)
  · exact .skip

/-- `letZeroEnv` is a valid `LetZeroEnvRel` choice. -/
theorem letZeroEnv_rel (σ : PEnv) (xs : List Ident) :
    LetZeroEnvRel σ xs (letZeroEnv σ xs) := by
  unfold letZeroEnv
  split
  · exact .zero rfl
  · exact .skip

/-- `assignEnv` is a valid `AssignEnvRel` choice — for any gate policy. -/
theorem assignEnv_rel (copyOK : Bool) (σ : PEnv) (xs : List Ident) (rhs' : Expr Op) :
    AssignEnvRel σ xs rhs' (assignEnv copyOK σ xs rhs') := by
  unfold assignEnv
  split
  · next x r hcl =>
      split
      · next hb => exact .refresh rfl hb (classifyProd_sub hcl)
      · exact .skip
  · exact .skip

mutual

/-- The statement transform inhabits the relation — for any gate policy. -/
theorem propStmt_rel (copyOK : Bool) (σ : PEnv) : ∀ s : Stmt Op,
    PropRel σ (propStmt copyOK σ s).2
      (.stmt s) (.stmt (propStmt copyOK σ s).1)
  | .block body => .blockS (propStmts_rel copyOK σ body)
  | .funDef _ ps rs body =>
      .funDefS (propStmts_rel (copyGate (ps.length + rs.length) body) [] body)
  | .letDecl xs none => .letNoneS (letZeroEnv_rel σ xs)
  | .letDecl xs (some e) =>
      .letSomeS (.fold) (letEnv_rel copyOK σ xs (rhsExpr σ e))
  | .assign xs e => .assignS (.fold) (assignEnv_rel copyOK σ xs (rhsExpr σ e))
  | .cond _ body => .condS (propStmts_rel copyOK σ body)
  | .switch _ cases dflt =>
      .switchS (propCases_rel copyOK σ cases) (propDflt_rel copyOK σ dflt)
  | .forLoop init _ post body =>
      .forS (propStmts_rel copyOK σ init) rfl
        (propStmts_rel copyOK _ post) (propStmts_rel copyOK _ body)
  | .exprStmt _ => .exprStmtS
  | .break => .breakS
  | .continue => .continueS
  | .leave => .leaveS

/-- The sequence transform inhabits the relation. -/
theorem propStmts_rel (copyOK : Bool) (σ : PEnv) : ∀ ss : List (Stmt Op),
    PropRel σ (propStmts copyOK σ ss).2
      (.stmts ss) (.stmts (propStmts copyOK σ ss).1)
  | [] => .nilSS
  | s :: rest =>
      .consSS (propStmt_rel copyOK σ s)
        (propStmts_rel copyOK (propStmt copyOK σ s).2 rest)

/-- The case-list transform inhabits the relation. -/
theorem propCases_rel (copyOK : Bool) (σ : PEnv) : ∀ cs : List (Literal × Block Op),
    PropRel σ σ
      (.cases cs) (.cases (propCases copyOK σ cs))
  | [] => .casesNil
  | (_, b) :: rest =>
      .casesCons (propStmts_rel copyOK σ b) (propCases_rel copyOK σ rest)

/-- The default transform inhabits the relation. -/
theorem propDflt_rel (copyOK : Bool) (σ : PEnv) : ∀ d : Option (Block Op),
    PropRel σ σ
      (.odflt d) (.odflt (propDflt copyOK σ d))
  | none => .odfltNone
  | some b => .odfltSome (propStmts_rel copyOK σ b)

end

/-! ### Variable-environment structure lemmas -/

/-- Lookup skips a prefix that does not bind `x`. -/
theorem VEnv.get_append_not_mem {ext W : VEnv D} {x : Ident}
    (h : x ∉ ext.map Prod.fst) : VEnv.get (ext ++ W) x = VEnv.get W x := by
  unfold VEnv.get
  rw [List.find?_append]
  have hnone : ext.find? (fun p => p.1 = x) = none := by
    apply List.find?_eq_none.mpr
    intro p hp
    simp only [decide_eq_true_eq]
    intro hx
    exact h (hx ▸ List.mem_map_of_mem hp)
  rw [hnone, Option.none_or]

/-- Lookup on a cons cell. -/
theorem VEnv.get_cons (p : Ident × U256) (V : VEnv D) (y : Ident) :
    VEnv.get (p :: V) y = if p.1 = y then some p.2 else VEnv.get V y := by
  unfold VEnv.get
  rw [List.find?_cons]
  by_cases h : p.1 = y <;> simp [h]

/-- In-place update does not change other keys' lookups. -/
theorem VEnv.get_set_ne {V : VEnv D} {x y : Ident} {v : U256} (h : y ≠ x) :
    VEnv.get (VEnv.set V x v) y = VEnv.get V y := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      rw [VEnv.set]
      split
      · next heq =>
          rw [VEnv.get_cons, VEnv.get_cons]
          have hx : ¬ (x = y) := fun hxy => h hxy.symm
          have hp : ¬ (p.1 = y) := heq ▸ hx
          simp [hx, hp]
      · rw [VEnv.get_cons, VEnv.get_cons, ih]

/-- One `foldl` of updates leaves unmentioned keys' lookups unchanged. -/
private theorem foldl_set_get_not_mem {x : Ident} :
    ∀ (l : List (Ident × U256)) (V : VEnv D), (∀ p ∈ l, p.1 ≠ x) →
      VEnv.get (l.foldl (fun acc p => VEnv.set acc p.1 p.2) V) x = VEnv.get V x := by
  intro l
  induction l with
  | nil => intro V _; rfl
  | cons p rest ih =>
      intro V hl
      rw [List.foldl_cons, ih _ (fun q hq => hl q (List.mem_cons_of_mem p hq))]
      exact VEnv.get_set_ne (fun hx => hl p (List.mem_cons_self ..) hx.symm)

/-- Multi-update does not change unmentioned keys' lookups. -/
theorem VEnv.get_setMany_not_mem {V : VEnv D} {xs : List Ident} {vs : List U256}
    {x : Ident} (h : x ∉ xs) :
    VEnv.get (VEnv.setMany V xs vs) x = VEnv.get V x := by
  refine foldl_set_get_not_mem (xs.zip vs) V ?_
  intro p hp hx
  rcases p with ⟨a, b⟩
  exact h (hx ▸ (List.of_mem_zip hp).1)

/-- Update of a *bound* key really lands. -/
theorem VEnv.get_set_self {V : VEnv D} {x : Ident} {v : U256}
    (h : (VEnv.get V x).isSome) : VEnv.get (VEnv.set V x v) x = some v := by
  induction V with
  | nil => simp [VEnv.get] at h
  | cons p rest ih =>
      rw [VEnv.set]
      split
      · next heq => rw [VEnv.get_cons]; simp
      · next hne =>
          rw [VEnv.get_cons] at h ⊢
          simp only [hne, if_false] at h ⊢
          exact ih h

/-! ### The environment frame

Executing statement-class code yields new bindings (keyed within the write set)
atop a key-preserving update of the input environment, unchanged outside the
write set. This is what carries a pruned tracked environment across nested
constructs, loop iterations, and `restore`. -/

/-- The frame relation between the input and output environments of a
statement-class execution with write set `ws`. -/
def EnvFrame (ws : List Ident) (V V' : VEnv D) : Prop :=
  ∃ ext W, V' = ext ++ W ∧ W.map Prod.fst = V.map Prod.fst ∧
    (∀ p ∈ ext, p.1 ∈ ws) ∧
    (∀ x : Ident, x ∉ ws → VEnv.get W x = VEnv.get V x)

namespace EnvFrame

theorem refl (ws : List Ident) (V : VEnv D) : EnvFrame ws V V :=
  ⟨[], V, rfl, rfl, by simp, fun _ _ => rfl⟩

theorem mono {ws ws' : List Ident} {V V' : VEnv D} (hsub : ∀ x ∈ ws, x ∈ ws')
    (h : EnvFrame ws V V') : EnvFrame ws' V V' := by
  obtain ⟨ext, W, hV', hkeys, hext, hget⟩ := h
  exact ⟨ext, W, hV', hkeys, fun p hp => hsub _ (hext p hp),
    fun x hx => hget x (fun hmem => hx (hsub _ hmem))⟩

/-- Unchanged lookups outside the write set. -/
theorem get_eq {ws : List Ident} {V V' : VEnv D} (h : EnvFrame ws V V')
    {x : Ident} (hx : x ∉ ws) : VEnv.get V' x = VEnv.get V x := by
  obtain ⟨ext, W, hV', hkeys, hext, hget⟩ := h
  subst hV'
  rw [VEnv.get_append_not_mem, hget x hx]
  intro hmem
  obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hmem
  exact hx (hpx ▸ hext p hp)

/-- The lengths never shrink. -/
theorem length_le {ws : List Ident} {V V' : VEnv D} (h : EnvFrame ws V V') :
    V.length ≤ V'.length := by
  obtain ⟨ext, W, hV', hkeys, _, _⟩ := h
  subst hV'
  have : W.length = V.length := by
    simpa using congrArg List.length hkeys
  simp [this]

/-- Frames compose along sequential execution. -/
theorem comp {ws : List Ident} {V V1 V2 : VEnv D}
    (h1 : EnvFrame ws V V1) (h2 : EnvFrame ws V1 V2) : EnvFrame ws V V2 := by
  obtain ⟨e1, W1, hV1, hk1, he1, hg1⟩ := h1
  obtain ⟨e2, W2, hV2, hk2, he2, hg2⟩ := h2
  subst hV1; subst hV2
  have hlenW2 : e1.length ≤ W2.length := by
    have : W2.length = e1.length + W1.length := by
      have := congrArg List.length hk2
      simpa using this
    omega
  have hsplit : W2 = W2.take e1.length ++ W2.drop e1.length := (List.take_append_drop _ _).symm
  have hkeysTake : (W2.take e1.length).map Prod.fst = e1.map Prod.fst := by
    have h1 : (W2.take e1.length).map Prod.fst = (W2.map Prod.fst).take e1.length := by
      simp [List.map_take]
    rw [h1, hk2]
    have : (e1.map Prod.fst).length = e1.length := by simp
    rw [List.map_append, List.take_append_of_le_length (by simp)]
    simp
  have hkeysDrop : (W2.drop e1.length).map Prod.fst = W1.map Prod.fst := by
    have h1 : (W2.drop e1.length).map Prod.fst = (W2.map Prod.fst).drop e1.length := by
      simp [List.map_drop]
    rw [h1, hk2, List.map_append, List.drop_append_of_le_length (by simp)]
    simp
  refine ⟨e2 ++ W2.take e1.length, W2.drop e1.length, by rw [List.append_assoc, ← hsplit],
    by rw [hkeysDrop, hk1], ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact he2 p hp
    · have : p.1 ∈ (W2.take e1.length).map Prod.fst := List.mem_map_of_mem hp
      rw [hkeysTake] at this
      obtain ⟨q, hq, hqp⟩ := List.mem_map.mp this
      exact hqp ▸ he1 q hq
  · intro x hx
    have hnotTake : x ∉ (W2.take e1.length).map Prod.fst := by
      rw [hkeysTake]
      intro hmem
      obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hmem
      exact hx (hqx ▸ he1 q hq)
    have hW2 : VEnv.get W2 x = VEnv.get (W2.drop e1.length) x := by
      conv_lhs => rw [hsplit]
      exact VEnv.get_append_not_mem hnotTake
    have hnotE1 : x ∉ e1.map Prod.fst := by
      intro hmem
      obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hmem
      exact hx (hqx ▸ he1 q hq)
    rw [← hW2, hg2 x hx, VEnv.get_append_not_mem hnotE1, hg1 x hx]

/-- A frame survives the enclosing block's `restore`. -/
theorem restore_frame {ws : List Ident} {V V' : VEnv D} (h : EnvFrame ws V V') :
    EnvFrame ws V (restore V V') := by
  obtain ⟨ext, W, hV', hkeys, hext, hget⟩ := h
  subst hV'
  have hlen : W.length = V.length := by simpa using congrArg List.length hkeys
  have hres : restore V (ext ++ W) = W := by
    unfold restore
    have : (ext ++ W).length - V.length = ext.length := by
      simp [hlen]
    rw [this, List.drop_left]
  rw [hres]
  exact ⟨[], W, rfl, hkeys, by simp, hget⟩

end EnvFrame

/-- Write set of a `Step` code class (statement classes only; expression
classes never touch the variable environment). -/
def codeWriteSet : Code Op → List Ident
  | .expr _ => []
  | .args _ => []
  | .stmt s => writeSetStmt s
  | .stmts ss => writeSetStmts ss
  | .loop _ post body => writeSetStmts post ++ writeSetStmts body

/-- The selected `switch` block's writes are among the branches' writes. -/
theorem selectSwitch_writeSet_subset (cv : U256) (cases : List (Literal × Block Op))
    (dflt : Option (Block Op)) :
    ∀ x ∈ writeSetStmts (selectSwitch D cv cases dflt),
      x ∈ writeSetCases cases ++ writeSetDflt dflt := by
  induction cases with
  | nil =>
      intro x hx
      cases dflt with
      | none => simp [selectSwitch, writeSetStmts] at hx
      | some b =>
          simp only [selectSwitch, List.find?_nil] at hx
          simp only [writeSetCases, writeSetDflt, List.nil_append]
          simpa using hx
  | cons head rest ih =>
      rcases head with ⟨l, b⟩
      intro x hx
      by_cases hcv : cv = (evmWithExternal calls creates).litValue l
      · rw [selectSwitch, List.find?_cons_of_pos (by simp [hcv])] at hx
        simp only [writeSetCases, List.append_assoc, List.mem_append]
        exact Or.inl hx
      · rw [selectSwitch, List.find?_cons_of_neg (by simp [hcv])] at hx
        have := ih x (by rw [selectSwitch]; exact hx)
        simp only [writeSetCases, List.append_assoc, List.mem_append] at this ⊢
        rcases this with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

/-- **The frame lemma**: a statement-class execution frames its write set —
new bindings are keyed within it, and lookups outside it are unchanged. -/
theorem Step.env_frame {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {code : Code Op} {res : Res D} (h : Step D funs V st code res) :
    ∀ {V' : VEnv D} {st' : EvmState} {o : Outcome}, res = .sres V' st' o →
      EnvFrame (codeWriteSet code) V V' := by
  induction h with
  | lit => exact fun h => nomatch h
  | var _ => exact fun h => nomatch h
  | builtinOk _ _ _ => exact fun h => nomatch h
  | builtinHalt _ _ _ => exact fun h => nomatch h
  | builtinArgsHalt _ _ => exact fun h => nomatch h
  | callOk _ _ _ _ _ _ _ => exact fun h => nomatch h
  | callHalt _ _ _ _ _ _ => exact fun h => nomatch h
  | callArgsHalt _ _ => exact fun h => nomatch h
  | argsNil => exact fun h => nomatch h
  | argsCons _ _ _ _ => exact fun h => nomatch h
  | argsRestHalt _ _ => exact fun h => nomatch h
  | argsHeadHalt _ _ _ _ => exact fun h => nomatch h
  | funDef =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | block _ ih =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact (ih rfl).restore_frame
  | @letZero funs V st vars =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      show EnvFrame vars V (bindZeros D vars ++ V)
      refine ⟨bindZeros D vars, V, rfl, rfl, ?_, fun _ _ => rfl⟩
      intro p hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      exact hx
  | @letVal funs V st vars e vals st1 _ hlen _ =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      show EnvFrame vars V (vars.zip vals ++ V)
      refine ⟨vars.zip vals, V, rfl, rfl, ?_, fun _ _ => rfl⟩
      intro p hp
      rcases p with ⟨a, b⟩
      exact (List.of_mem_zip hp).1
  | letHalt _ _ =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | @assignVal funs V st vars e vals st1 _ hlen _ =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      show EnvFrame vars V (VEnv.setMany V vars vals)
      exact ⟨[], VEnv.setMany V vars vals, rfl, VEnv.setMany_keys V vars vals,
        fun p hp => absurd hp (List.not_mem_nil),
        fun x hx => VEnv.get_setMany_not_mem hx⟩
  | assignHalt _ _ =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | exprStmt _ _ =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | exprStmtHalt _ _ =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | ifTrue _ _ _ _ ihb =>
      intro V' st' o hres
      exact ihb hres
  | ifFalse _ _ _ =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | ifHalt _ _ =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | @switchExec funs V st c cases dflt cv st1 V2 st2 o2 _ _ _ ihb =>
      intro V' st' o hres
      exact (ihb hres).mono (selectSwitch_writeSet_subset cv cases dflt)
  | switchHalt _ _ =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | @forLoop funs V st init c post body Vinit stinit Vend stend o2 hinit hloop ihinit ihloop =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      show EnvFrame (writeSetStmts init ++ writeSetStmts post ++ writeSetStmts body)
        V (restore V Vend)
      have h1 : EnvFrame (writeSetStmts init ++ writeSetStmts post ++ writeSetStmts body)
          V Vinit :=
        (ihinit rfl).mono (fun x hx => by
          simp only [List.mem_append]
          exact Or.inl (Or.inl hx))
      have h2 : EnvFrame (writeSetStmts init ++ writeSetStmts post ++ writeSetStmts body)
          Vinit Vend :=
        (ihloop rfl).mono (fun x hx => by
          simp only [codeWriteSet, List.mem_append] at hx ⊢
          tauto)
      exact (h1.comp h2).restore_frame
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      show EnvFrame (writeSetStmts init ++ writeSetStmts post ++ writeSetStmts body)
        V (restore V Vinit)
      refine EnvFrame.restore_frame ((ihinit rfl).mono (fun x hx => ?_))
      simp only [List.mem_append]
      exact Or.inl (Or.inl hx)
  | «break» =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | «continue» =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | leave =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | seqNil =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | @seqCons funs V st s rest V1 st1 V2 st2 o2 _ _ ihs ihrest =>
      intro V' st' o hres
      show EnvFrame (writeSetStmt s ++ writeSetStmts rest) V V'
      have h1 : EnvFrame (writeSetStmt s ++ writeSetStmts rest) V V1 :=
        (ihs rfl).mono (fun x hx => List.mem_append.mpr (Or.inl hx))
      have h2 : EnvFrame (writeSetStmt s ++ writeSetStmts rest) V1 V' :=
        (ihrest hres).mono (fun x hx => List.mem_append.mpr (Or.inr hx))
      exact h1.comp h2
  | @seqStop funs V st s rest V1 st1 o2 _ _ ihs =>
      intro V' st' o hres
      show EnvFrame (writeSetStmt s ++ writeSetStmts rest) V V'
      exact (ihs hres).mono (fun x hx => List.mem_append.mpr (Or.inl hx))
  | loopDone _ _ _ =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | loopCondHalt _ _ =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact EnvFrame.refl _ _
  | @loopStep funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o2
      _ _ _ _ _ _ ihc ihb ihp ihr =>
      intro V' st' o hres
      show EnvFrame (writeSetStmts post ++ writeSetStmts body) V V'
      have h1 : EnvFrame (writeSetStmts post ++ writeSetStmts body) V Vb :=
        (ihb rfl).mono (fun x hx => List.mem_append.mpr (Or.inr hx))
      have h2 : EnvFrame (writeSetStmts post ++ writeSetStmts body) Vb Vp :=
        (ihp rfl).mono (fun x hx => List.mem_append.mpr (Or.inl hx))
      exact (h1.comp h2).comp (ihr hres)
  | @loopPostHalt funs V st c post body cv st1 Vb stb ob Vp stp
      _ _ _ _ _ ihc ihb ihp =>
      intro V' st' o hres
      show EnvFrame (writeSetStmts post ++ writeSetStmts body) V V'
      have h1 : EnvFrame (writeSetStmts post ++ writeSetStmts body) V Vb :=
        (ihb rfl).mono (fun x hx => List.mem_append.mpr (Or.inr hx))
      have h2 : EnvFrame (writeSetStmts post ++ writeSetStmts body) Vb V' :=
        (ihp hres).mono (fun x hx => List.mem_append.mpr (Or.inl hx))
      exact h1.comp h2
  | loopBreak _ _ _ _ ihb =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact (ihb rfl).mono (fun x hx => List.mem_append.mpr (Or.inr hx))
  | loopLeave _ _ _ _ ihb =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact (ihb rfl).mono (fun x hx => List.mem_append.mpr (Or.inr hx))
  | loopBodyHalt _ _ _ _ ihb =>
      intro V' st' o hres
      injection hres with h1 h2 h3
      subst h1
      exact (ihb rfl).mono (fun x hx => List.mem_append.mpr (Or.inr hx))

/-! ### The compatibility invariant -/

/-- A tracked entry agrees with the runtime environment: the key is bound and
holds the entry's denotation. -/
def RhsHolds (V : VEnv D) : Ident × PRhs → Prop
  | (x, .lit n) => VEnv.get V x = some (litValue (.number n))
  | (x, .var y) => ∃ v : U256, VEnv.get V x = some v ∧ VEnv.get V y = some v

/-- Every tracked entry agrees with the runtime environment. -/
def Compat (V : VEnv D) (σ : PEnv) : Prop := ∀ p ∈ σ, RhsHolds V p

/-- The empty tracked environment is universally compatible. -/
theorem Compat.nil (V : VEnv D) : Compat V [] :=
  fun _ hp => absurd hp (List.not_mem_nil)

/-- Compatibility restricts to pruned environments. -/
theorem Compat.restrict {V : VEnv D} {σ : PEnv} (h : Compat V σ)
    (ws : List Ident) : Compat V (prune σ ws) :=
  fun p hp => h p (List.mem_of_mem_filter hp)

/-- An entry surviving a prune mentions nothing in the write set. -/
theorem prune_not_hit {σ : PEnv} {ws : List Ident} {p : Ident × PRhs}
    (hp : p ∈ prune σ ws) : entryHits ws p = false := by
  have := List.of_mem_filter hp
  simpa using this

/-- Compatibility transports across an execution frame, for the entries the
frame's write set cannot touch. -/
theorem Compat.of_frame {V V' : VEnv D} {σ : PEnv} {ws : List Ident}
    (h : Compat V σ) (hf : EnvFrame ws V V') :
    Compat V' (prune σ ws) := by
  intro p hp
  have hhit := prune_not_hit hp
  have hbase := h p (List.mem_of_mem_filter hp)
  rcases p with ⟨x, rhs⟩
  cases rhs with
  | lit n =>
      have hx : x ∉ ws := by
        intro hmem
        simp [entryHits, hmem] at hhit
      simpa [RhsHolds, hf.get_eq hx] using hbase
  | var y =>
      have hx : x ∉ ws ∧ y ∉ ws := by
        constructor <;> (intro hmem; simp [entryHits, hmem] at hhit)
      obtain ⟨v, hvx, hvy⟩ := hbase
      exact ⟨v, by rw [hf.get_eq hx.1]; exact hvx, by rw [hf.get_eq hx.2]; exact hvy⟩

/-- An already-stable tracked environment survives its own prune unchanged —
the `for`-loop environment is stable by construction. -/
theorem Compat.of_frame_stable {V V' : VEnv D} {σ : PEnv} {ws : List Ident}
    (hstable : prune σ ws = σ)
    (h : Compat V σ) (hf : EnvFrame ws V V') :
    Compat V' σ := by
  have := h.of_frame hf
  rwa [hstable] at this

/-! ### Small facts about the transform's ingredients -/

/-- `classify` inversion: a literal classification pins the syntax. -/
theorem classify_lit {e : Expr Op} {n : Nat} (h : classify e = some (.lit n)) :
    e = .lit (.number n) := by
  unfold classify at h
  split at h <;> simp_all

/-- `classify` inversion: a copy classification pins the syntax. -/
theorem classify_var {e : Expr Op} {y : Ident} (h : classify e = some (.var y)) :
    e = .var y := by
  unfold classify at h
  split at h <;> simp_all

/-- A successful tracked lookup exhibits a member entry. -/
theorem mem_of_lookupEnv {σ : PEnv} {x : Ident} {r : PRhs}
    (h : lookupEnv σ x = some r) : (x, r) ∈ σ := by
  unfold lookupEnv at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨p, hfind, hp⟩ := h
  have hmem := List.mem_of_find?_eq_some hfind
  have hkey : p.1 = x := by simpa using List.find?_some hfind
  have : p = (x, r) := by
    rcases p with ⟨a, b⟩
    simp_all
  exact this ▸ hmem

mutual

/-- Substitution with an empty tracked environment is the identity. -/
theorem substExpr_nil : ∀ e : Expr Op, substExpr [] e = e
  | .lit _ => rfl
  | .var _ => rfl
  | .builtin _ args => by rw [substExpr, substArgs_nil args]
  | .call _ args => by rw [substExpr, substArgs_nil args]

/-- Argument substitution with an empty tracked environment is the identity. -/
theorem substArgs_nil : ∀ es : List (Expr Op), substArgs [] es = es
  | [] => rfl
  | e :: rest => by rw [substArgs, substExpr_nil e, substArgs_nil rest]

end

/-- Pruning is idempotent — the `for`-loop environment is stable. -/
theorem prune_idem (σ : PEnv) (ws : List Ident) : prune (prune σ ws) ws = prune σ ws := by
  unfold prune
  rw [List.filter_filter]
  simp

/-- Singleton multi-update is a plain update. -/
theorem VEnv.setMany_singleton (V : VEnv D) (x : Ident) (v : U256) :
    VEnv.setMany V [x] [v] = VEnv.set V x v := rfl

/-- The rhs fold is a sound local rewrite. -/
theorem foldRhs_equiv (e : Expr Op) :
    EquivExpr D e (foldRhs e) := by
  cases e with
  | lit l => exact EquivExpr.refl _
  | var x => exact EquivExpr.refl _
  | call f args => exact EquivExpr.refl _
  | builtin op args =>
      cases hlits : asLits args with
      | none =>
          have hred : foldRhs (.builtin op args) = .builtin op args := by
            simp only [foldRhs, hlits]
          rw [hred]
          exact EquivExpr.refl _
      | some lits =>
          cases hfold : pureFold op lits with
          | none =>
              have hred : foldRhs (.builtin op args) = .builtin op args := by
                simp only [foldRhs, hlits, hfold]
              rw [hred]
              exact EquivExpr.refl _
          | some l =>
              have hred : foldRhs (.builtin op args) = .lit l := by
                simp only [foldRhs, hlits, hfold]
              rw [hred, asLits_map hlits]
              exact fold_equiv hfold

/-- Reconstruct the evaluation of a *source* argument list whose substitution
is all-literal: each source argument is a literal or a tracked variable, so it
evaluates (state unchanged) to the substituted literal's value. -/
theorem substArgs_lits_eval {σ : PEnv} {V : VEnv D}
    (hc : Compat V σ) (funs : FunEnv D) (st : EvmState) :
    ∀ {srcArgs : List (Expr Op)} {lits : List Literal},
      substArgs σ srcArgs = lits.map Expr.lit →
      Step D funs V st (.args srcArgs) (.eres (.vals (lits.map litValue) st)) := by
  intro srcArgs
  induction srcArgs with
  | nil =>
      intro lits h
      have : lits = [] := by
        cases lits with
        | nil => rfl
        | cons l rest => simp [substArgs] at h
      subst this
      exact Step.argsNil
  | cons e rest ih =>
      intro lits h
      cases lits with
      | nil => simp [substArgs] at h
      | cons l ls =>
          rw [substArgs, List.map_cons] at h
          injection h with he hrest
          have hs : Step D funs V st (.expr e) (.eres (.vals [litValue l] st)) := by
            cases e with
            | lit l0 =>
                have : l0 = l := by simpa [substExpr] using he
                subst this
                exact Step.lit
            | var x =>
                rw [substExpr] at he
                cases hlook : lookupEnv σ x with
                | none => simp [hlook] at he
                | some r =>
                    cases r with
                    | lit n =>
                        have hl : Literal.number n = l := by
                          simpa [hlook, PRhs.toExpr] using he
                        have hmem := mem_of_lookupEnv hlook
                        have := hc _ hmem
                        rw [RhsHolds] at this
                        rw [← hl]
                        exact Step.var this
                    | var y => simp [hlook, PRhs.toExpr] at he
            | builtin _ _ => rw [substExpr] at he; cases he
            | call _ _ => rw [substExpr] at he; cases he
          exact Step.argsCons (ih hrest) hs

/-! ### The function-environment relation

Scopes of equal names and signatures whose bodies are `PropRel []`-related.
Purely syntactic (no semantic equivalence is stored), so the `call` cases of
the simulation recurse directly on the callee-body sub-derivation. -/

/-- Declarations with equal signatures and `PropRel []`-related bodies. -/
def PFDeclRel (d₁ d₂ : FDecl D) : Prop :=
  d₁.params = d₂.params ∧ d₁.rets = d₂.rets ∧
    ∃ σ', PropRel []  σ'
      (.stmts d₁.body) (.stmts d₂.body)

/-- Scopes related pairwise: equal names, `PFDeclRel` declarations. -/
def PScopeRel (s₁ s₂ : FScope D) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ PFDeclRel (calls := calls) (creates := creates) p.2 q.2) s₁ s₂

/-- Function environments related scope-by-scope. -/
def PFunsRel (f₁ f₂ : FunEnv D) : Prop :=
  List.Forall₂ (PScopeRel (calls := calls) (creates := creates)) f₁ f₂

/-! #### The identity derivation (reflexivity at the empty environment) -/

mutual

/-- Every statement is `PropRel []`-related to itself (all actions skipped). -/
theorem PropRel.reflStmt : ∀ s : Stmt Op,
    PropRel [] [] (.stmt s) (.stmt s)
  | .block body => by
      have := PropRel.blockS (reflStmts body)
      simpa [prune] using this
  | .funDef n ps rs body => .funDefS (reflStmts body)
  | .letDecl xs none => by
      have h : LetZeroEnvRel ([] : PEnv) xs (prune [] xs) := .skip
      have : prune ([] : PEnv) xs = [] := rfl
      exact this ▸ PropRel.letNoneS h
  | .letDecl xs (some e) => by
      have hrhs : RhsRel [] e e := by
        have := RhsRel.subst (σ := []) (e := e)
        rwa [substExpr_nil] at this
      have henv : LetEnvRel ([] : PEnv) xs e (prune [] xs) := .skip
      have hpr : prune ([] : PEnv) xs = [] := rfl
      exact hpr ▸ PropRel.letSomeS hrhs henv
  | .assign xs e => by
      have hrhs : RhsRel [] e e := by
        have := RhsRel.subst (σ := []) (e := e)
        rwa [substExpr_nil] at this
      have henv : AssignEnvRel ([] : PEnv) xs e (prune [] xs) := .skip
      have hpr : prune ([] : PEnv) xs = [] := rfl
      exact hpr ▸ PropRel.assignS hrhs henv
  | .cond c body => by
      have := PropRel.condS (c := c) (reflStmts body)
      simpa [prune, substExpr_nil] using this
  | .switch c cases dflt => by
      have := PropRel.switchS (c := c)
        (reflCases cases) (reflDflt dflt)
      simpa [prune, substExpr_nil] using this
  | .forLoop init c post body => by
      have hL : prune ([] : PEnv) (writeSetStmts post ++ writeSetStmts body) = [] := rfl
      have := PropRel.forS (c := c)
        (reflStmts init) hL.symm (reflStmts post) (reflStmts body)
      simpa [prune, substExpr_nil] using this
  | .exprStmt e => by
      have := PropRel.exprStmtS (σ := []) (e := e)
      simpa [substExpr_nil] using this
  | .break => .breakS
  | .continue => .continueS
  | .leave => .leaveS

/-- Every sequence is `PropRel []`-related to itself. -/
theorem PropRel.reflStmts : ∀ ss : List (Stmt Op),
    PropRel [] [] (.stmts ss) (.stmts ss)
  | [] => .nilSS
  | s :: rest => .consSS (reflStmt s) (reflStmts rest)

/-- Every case list is `PropRel []`-related to itself. -/
theorem PropRel.reflCases : ∀ cs : List (Literal × Block Op),
    PropRel [] [] (.cases cs) (.cases cs)
  | [] => .casesNil
  | (_, b) :: rest => .casesCons (reflStmts b) (reflCases rest)

/-- Every default is `PropRel []`-related to itself. -/
theorem PropRel.reflDflt : ∀ d : Option (Block Op),
    PropRel [] [] (.odflt d) (.odflt d)
  | none => .odfltNone
  | some b => .odfltSome (reflStmts b)

end

theorem PFDeclRel.refl (d : FDecl D) : PFDeclRel (calls := calls) (creates := creates) d d :=
  ⟨rfl, rfl, [], PropRel.reflStmts d.body⟩

theorem PScopeRel.refl (s : FScope D) : PScopeRel (calls := calls) (creates := creates) s s := by
  induction s with
  | nil => exact .nil
  | cons p t ih => exact .cons ⟨rfl, PFDeclRel.refl _⟩ ih

theorem PFunsRel.refl (f : FunEnv D) : PFunsRel (calls := calls) (creates := creates) f f := by
  induction f with
  | nil => exact .nil
  | cons s t ih => exact .cons (PScopeRel.refl _) ih

/-! #### Hoisting respects the relation -/

/-- Related sequences hoist related function scopes: the relation preserves
statement constructors, so `hoist` collects pairwise-related declarations. -/
theorem PropRel.hoist_scopeRel {σ σ' : PEnv} {pc pc' : PCode Op}
    (h : PropRel σ σ' pc pc') :
    ∀ {ss ss' : List (Stmt Op)}, pc = .stmts ss → pc' = .stmts ss' →
      PScopeRel (calls := calls) (creates := creates) (hoist D ss) (hoist D ss') := by
  induction h with
  | nilSS =>
      intro ss ss' hss hss'
      injection hss with h1; injection hss' with h2
      subst h1; subst h2
      exact .nil
  | consSS hs _ _ ihrest =>
      intro ss ss' hss hss'
      injection hss with h1; injection hss' with h2
      subst h1; subst h2
      have htail := ihrest rfl rfl
      cases hs with
      | funDefS hbody =>
          exact .cons ⟨rfl, rfl, rfl, _, hbody⟩ htail
      | blockS _ => simpa [hoist] using htail
      | letSomeS _ _ => simpa [hoist] using htail
      | letNoneS _ => simpa [hoist] using htail
      | assignS _ _ => simpa [hoist] using htail
      | condS _ => simpa [hoist] using htail
      | switchS _ _ => simpa [hoist] using htail
      | forS _ _ _ _ => simpa [hoist] using htail
      | exprStmtS => simpa [hoist] using htail
      | breakS => simpa [hoist] using htail
      | continueS => simpa [hoist] using htail
      | leaveS => simpa [hoist] using htail
  | expr _ => exact fun h _ => nomatch h
  | args => exact fun h _ => nomatch h
  | blockS _ _ => exact fun h _ => nomatch h
  | funDefS _ _ => exact fun h _ => nomatch h
  | letSomeS _ _ => exact fun h _ => nomatch h
  | letNoneS _ => exact fun h _ => nomatch h
  | assignS _ _ => exact fun h _ => nomatch h
  | condS _ _ => exact fun h _ => nomatch h
  | switchS _ _ _ _ => exact fun h _ => nomatch h
  | forS _ _ _ _ _ _ _ => exact fun h _ => nomatch h
  | exprStmtS => exact fun h _ => nomatch h
  | breakS => exact fun h _ => nomatch h
  | continueS => exact fun h _ => nomatch h
  | leaveS => exact fun h _ => nomatch h
  | loopL _ _ _ _ _ => exact fun h _ => nomatch h
  | casesNil => exact fun h _ => nomatch h
  | casesCons _ _ _ _ => exact fun h _ => nomatch h
  | odfltNone => exact fun h _ => nomatch h
  | odfltSome _ _ => exact fun h _ => nomatch h

/-! #### Lookups transport across the relation, in both directions -/

/-- A scope lookup transports across `PScopeRel` (both directions at once). -/
theorem pScopeRel_find {s₁ s₂ : FScope D}
    (h : PScopeRel (calls := calls) (creates := creates) s₁ s₂) (fn : Ident) :
    (s₁.find? (fun p => p.1 = fn) = none ∧ s₂.find? (fun p => p.1 = fn) = none) ∨
    (∃ p q, s₁.find? (fun p => p.1 = fn) = some p ∧ s₂.find? (fun p => p.1 = fn) = some q ∧
      p.1 = q.1 ∧ PFDeclRel (calls := calls) (creates := creates) p.2 q.2) := by
  induction h with
  | nil => left; simp
  | @cons p q u₁ u₂ hpq _ ih =>
      by_cases hp : p.1 = fn
      · right
        refine ⟨p, q, ?_, ?_, hpq.1, hpq.2⟩
        · exact List.find?_cons_of_pos (by simp [hp])
        · exact List.find?_cons_of_pos (by simp [← hpq.1, hp])
      · rw [List.find?_cons_of_neg (by simp [hp]),
            List.find?_cons_of_neg (by simp [← hpq.1, hp])]
        exact ih

/-- `lookupFun` transports forward across `PFunsRel`. -/
theorem lookupFun_pFunsRel {f₁ f₂ : FunEnv D}
    (hR : PFunsRel (calls := calls) (creates := creates) f₁ f₂) :
    ∀ {fn : Ident} {decl : FDecl D} {cenv : FunEnv D},
      lookupFun f₁ fn = some (decl, cenv) →
      ∃ decl' cenv', lookupFun f₂ fn = some (decl', cenv') ∧
        decl'.params = decl.params ∧ decl'.rets = decl.rets ∧
        (∃ σ', PropRel [] σ'
          (.stmts decl.body) (.stmts decl'.body)) ∧
        PFunsRel (calls := calls) (creates := creates) cenv cenv' := by
  induction hR with
  | nil => intro fn decl cenv h; simp [lookupFun] at h
  | @cons s₁ s₂ t₁ t₂ hs hR' ih =>
      intro fn decl cenv h
      rcases pScopeRel_find hs fn with ⟨hn₁, hn₂⟩ | ⟨p, q, hp₁, hp₂, hkey, hd⟩
      · rw [lookupFun, hn₁] at h
        obtain ⟨decl', cenv', hl', hpar, hret, hbody, hRc⟩ := ih h
        exact ⟨decl', cenv', by rw [lookupFun, hn₂]; exact hl', hpar, hret, hbody, hRc⟩
      · rw [lookupFun, hp₁] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hd_eq, hcenv_eq⟩ := h
        subst hd_eq; subst hcenv_eq
        exact ⟨q.2, s₂ :: t₂, by rw [lookupFun, hp₂], hd.1.symm, hd.2.1.symm,
          hd.2.2, List.Forall₂.cons hs hR'⟩

/-- `lookupFun` transports backward across `PFunsRel` (the relation's
orientation on bodies is kept source→target). -/
theorem lookupFun_pFunsRel_bwd {f₁ f₂ : FunEnv D}
    (hR : PFunsRel (calls := calls) (creates := creates) f₁ f₂) :
    ∀ {fn : Ident} {decl' : FDecl D} {cenv' : FunEnv D},
      lookupFun f₂ fn = some (decl', cenv') →
      ∃ decl cenv, lookupFun f₁ fn = some (decl, cenv) ∧
        decl'.params = decl.params ∧ decl'.rets = decl.rets ∧
        (∃ σ', PropRel [] σ'
          (.stmts decl.body) (.stmts decl'.body)) ∧
        PFunsRel (calls := calls) (creates := creates) cenv cenv' := by
  induction hR with
  | nil => intro fn decl' cenv' h; simp [lookupFun] at h
  | @cons s₁ s₂ t₁ t₂ hs hR' ih =>
      intro fn decl' cenv' h
      rcases pScopeRel_find hs fn with ⟨hn₁, hn₂⟩ | ⟨p, q, hp₁, hp₂, hkey, hd⟩
      · rw [lookupFun, hn₂] at h
        obtain ⟨decl, cenv, hl, hpar, hret, hbody, hRc⟩ := ih h
        exact ⟨decl, cenv, by rw [lookupFun, hn₁]; exact hl, hpar, hret, hbody, hRc⟩
      · rw [lookupFun, hp₂] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hd_eq, hcenv_eq⟩ := h
        subst hd_eq; subst hcenv_eq
        exact ⟨p.2, s₁ :: t₁, by rw [lookupFun, hp₁], hd.1.symm, hd.2.1.symm,
          hd.2.2, List.Forall₂.cons hs hR'⟩

/-! ### Leaf evaluation of substituted reads -/

/-- Substituting a variable read never produces a builtin or a call. -/
theorem foldRhs_substVar (σ : PEnv) (x : Ident) :
    foldRhs (substExpr σ (.var x)) = substExpr σ (.var x) := by
  rw [substExpr]
  cases lookupEnv σ x with
  | none => rfl
  | some r => cases r <;> rfl

@[simp] theorem foldRhs_lit (l : Literal) : foldRhs (Expr.lit (Op := Op) l) = .lit l := rfl

@[simp] theorem foldRhs_call (f : Ident) (es : List (Expr Op)) :
    foldRhs (Expr.call f es) = .call f es := rfl

/-- Forward: a substituted variable read evaluates to the original's value. -/
theorem substVar_eval_fwd {σ : PEnv} {V : VEnv D} {x : Ident} {v : U256}
    (hc : Compat V σ)
    (hv : VEnv.get V x = some v) (funs : FunEnv D) (st : EvmState) :
    Step D funs V st (.expr (substExpr σ (.var x))) (.eres (.vals [v] st)) := by
  rw [substExpr]
  cases hlook : lookupEnv σ x with
  | none => exact Step.var hv
  | some r =>
      have hholds := hc _ (mem_of_lookupEnv hlook)
      cases r with
      | lit n =>
          rw [RhsHolds] at hholds
          have hveq : v = litValue (.number n) := by
            rw [hv] at hholds; injection hholds
          simp only [PRhs.toExpr]; rw [hveq]
          exact Step.lit
      | var y =>
          obtain ⟨w, hwx, hwy⟩ := hholds
          have hveq : v = w := by rw [hv] at hwx; injection hwx
          simp only [PRhs.toExpr]
          exact Step.var (hveq ▸ hwy)

/-- Backward: an evaluation of a substituted variable read is an evaluation of
the original read (the tracked entry supplies boundness). -/
theorem substVar_eval_bwd {σ : PEnv} {V : VEnv D} {x : Ident} {r : EResult D}
    {funs : FunEnv D} {st : EvmState}
    (hc : Compat V σ)
    (h : Step D funs V st (.expr (substExpr σ (.var x))) (.eres r)) :
    Step D funs V st (.expr (.var x)) (.eres r) := by
  rw [substExpr] at h
  cases hlook : lookupEnv σ x with
  | none => rwa [hlook] at h
  | some rhs =>
      rw [hlook] at h
      have hholds := hc _ (mem_of_lookupEnv hlook)
      cases rhs with
      | lit n =>
          rw [RhsHolds] at hholds
          simp only [PRhs.toExpr] at h
          cases h with
          | lit => exact Step.var hholds
      | var y =>
          obtain ⟨w, hwx, hwy⟩ := hholds
          simp only [PRhs.toExpr] at h
          cases h with
          | var hvy =>
              rw [hwy] at hvy
              injection hvy with hv
              exact Step.var (hv ▸ hwx)

/-- What the simulation claims about the tracked out-environment, per class:
statement classes re-establish compatibility on `normal`; the loop class keeps
its (stable) environment compatible at every outcome. -/
def compatAfter (σ' : PEnv) (pc : PCode Op) (V' : VEnv D) (o : Outcome) : Prop :=
  match pc with
  | .stmt _ => o = .normal → Compat V' σ'
  | .stmts _ => o = .normal → Compat V' σ'
  | .loop _ _ _ => Compat V' σ'
  | _ => True

/-- The `switch` selection of related case lists/defaults is a related block. -/
theorem PropRel.selectRel {σ τc τd : PEnv} {cases cases' : List (Literal × Block Op)}
    {dflt dflt' : Option (Block Op)}
    (hcs : PropRel σ τc (.cases cases) (.cases cases'))
    (hd : PropRel σ τd (.odflt dflt) (.odflt dflt'))
    (cv : U256) :
    ∃ σsel, PropRel σ σsel
      (.stmts (selectSwitch D cv cases dflt))
      (.stmts (selectSwitch D cv cases' dflt')) := by
  induction cases generalizing cases' with
  | nil =>
      cases hcs
      cases hd with
      | odfltNone =>
          refine ⟨σ, ?_⟩
          show PropRel σ σ (.stmts (Option.getD none [])) (.stmts (Option.getD none []))
          exact PropRel.nilSS
      | odfltSome hb =>
          exact ⟨_, by simpa [selectSwitch] using hb⟩
  | cons head rest ih =>
      rcases head with ⟨l, b⟩
      cases hcs with
      | casesCons hb hrest =>
          by_cases hcv : cv = (evmWithExternal calls creates).litValue l
          · rw [selectSwitch, List.find?_cons_of_pos (by simp [hcv]),
                selectSwitch, List.find?_cons_of_pos (by simp [hcv])]
            exact ⟨_, hb⟩
          · obtain ⟨σsel, hsel⟩ := ih hrest
            refine ⟨σsel, ?_⟩
            rw [selectSwitch, List.find?_cons_of_neg (by simp [hcv]),
                selectSwitch, List.find?_cons_of_neg (by simp [hcv])]
            rw [selectSwitch] at hsel
            exact hsel

/-! ### The master simulation

`prop_fwd`: a derivation of the source transports to a derivation of the
propagated program with the *same* result, re-establishing `Compat` for the
threaded environment. `prop_bwd` (below) is the converse. Together they
discharge `Sound`. -/

/-- Embed `Step`'s code classes into the relation's classes. -/
def toPCode : Code Op → PCode Op
  | .expr e => .expr e
  | .args es => .args es
  | .stmt s => .stmt s
  | .stmts ss => .stmts ss
  | .loop c post body => .loop c post body

/-- Project back (junk on the two extra classes, which never relate to an
embedded `Code`). -/
def ofPCode : PCode Op → Code Op
  | .expr e => .expr e
  | .args es => .args es
  | .stmt s => .stmt s
  | .stmts ss => .stmts ss
  | .loop c post body => .loop c post body
  | .cases _ => .stmts []
  | .odflt _ => .stmts []

/-- **Forward simulation.** A source derivation, a propagation of its code, a
related function environment, and a compatible tracked environment yield the
same result for the propagated code — and compatibility of the threaded
environment out. -/
theorem prop_fwd {funs₁ : FunEnv D} {V : VEnv D} {st : EvmState}
    {code : Code Op} {res : Res D} (h : Step D funs₁ V st code res) :
    ∀ {funs₂ : FunEnv D} {σ σ' : PEnv} {pc' : PCode Op},
      PFunsRel funs₁ funs₂ → PropRel σ σ' (toPCode code) pc' → Compat V σ →
      Step D funs₂ V st (ofPCode pc') res ∧
        (∀ V' st' o, res = .sres V' st' o → compatAfter σ' (toPCode code) V' o) := by
  induction h with
  | @lit funs V st l =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | expr hrhs =>
          refine ⟨?_, fun _ _ _ h => nomatch h⟩
          cases hrhs with
          | subst => exact Step.lit
          | fold => exact Step.lit
  | @var funs V st x v hv =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | expr hrhs =>
          refine ⟨?_, fun _ _ _ h => nomatch h⟩
          cases hrhs with
          | subst => exact substVar_eval_fwd hc hv funs₂ st
          | fold =>
              show Step D funs₂ V st (.expr (rhsExpr σ (.var x))) _
              rw [rhsExpr, foldRhs_substVar]
              exact substVar_eval_fwd hc hv funs₂ st
  | @builtinOk funs V st op args argvals st1 rets st2 ha hb iha =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | expr hrhs =>
          refine ⟨?_, fun _ _ _ h => nomatch h⟩
          have hargs := (iha hR (PropRel.args) hc).1
          have hsub : Step D funs₂ V st (.expr (substExpr σ (.builtin op args)))
              (.eres (.vals rets st2)) := by
            rw [substExpr]
            exact Step.builtinOk hargs hb
          cases hrhs with
          | subst => exact hsub
          | fold =>
              show Step D funs₂ V st (.expr (rhsExpr σ (.builtin op args))) _
              rw [rhsExpr]
              exact ((foldRhs_equiv (substExpr σ (.builtin op args))) funs₂ V st _).mp hsub
  | @builtinHalt funs V st op args argvals st1 st2 ha hb iha =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | expr hrhs =>
          refine ⟨?_, fun _ _ _ h => nomatch h⟩
          have hargs := (iha hR (PropRel.args) hc).1
          have hsub : Step D funs₂ V st (.expr (substExpr σ (.builtin op args)))
              (.eres (.halt st2)) := by
            rw [substExpr]
            exact Step.builtinHalt hargs hb
          cases hrhs with
          | subst => exact hsub
          | fold =>
              show Step D funs₂ V st (.expr (rhsExpr σ (.builtin op args))) _
              rw [rhsExpr]
              exact ((foldRhs_equiv (substExpr σ (.builtin op args))) funs₂ V st _).mp hsub
  | @builtinArgsHalt funs V st op args st1 ha iha =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | expr hrhs =>
          refine ⟨?_, fun _ _ _ h => nomatch h⟩
          have hargs := (iha hR (PropRel.args) hc).1
          have hsub : Step D funs₂ V st (.expr (substExpr σ (.builtin op args)))
              (.eres (.halt st1)) := by
            rw [substExpr]
            exact Step.builtinArgsHalt hargs
          cases hrhs with
          | subst => exact hsub
          | fold =>
              show Step D funs₂ V st (.expr (rhsExpr σ (.builtin op args))) _
              rw [rhsExpr]
              exact ((foldRhs_equiv (substExpr σ (.builtin op args))) funs₂ V st _).mp hsub
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o ha hl hlen hbody ho iha ihbody =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | expr hrhs =>
          refine ⟨?_, fun _ _ _ h => nomatch h⟩
          have hargs := (iha hR (PropRel.args) hc).1
          obtain ⟨decl', cenv', hl', hpar, hret, ⟨σb, hbodyRel⟩, hRc⟩ := lookupFun_pFunsRel hR hl
          have hbody' := (ihbody hRc (PropRel.blockS hbodyRel) (Compat.nil _)).1
          have hbody'' : Step D cenv' (decl'.params.zip argvals ++ bindZeros D decl'.rets) st1
              (.stmt (.block decl'.body)) (.sres Vend st2 o) := by
            rw [hpar, hret]; exact hbody'
          have hres := Step.callOk (fn := fn) hargs hl' (by rw [hpar]; exact hlen) hbody'' ho
          rw [hret] at hres
          have hsub : Step D funs₂ V st (.expr (substExpr σ (.call fn args)))
              (.eres (.vals (decl.rets.map
                (fun r => (VEnv.get Vend r).getD (evmWithExternal calls creates).zero)) st2)) := by
            rw [substExpr]
            exact hres
          cases hrhs with
          | subst => exact hsub
          | fold =>
              show Step D funs₂ V st (.expr (rhsExpr σ (.call fn args))) _
              rw [rhsExpr, substExpr, foldRhs_call]
              rw [substExpr] at hsub
              exact hsub
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hl hlen hbody iha ihbody =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | expr hrhs =>
          refine ⟨?_, fun _ _ _ h => nomatch h⟩
          have hargs := (iha hR (PropRel.args) hc).1
          obtain ⟨decl', cenv', hl', hpar, hret, ⟨σb, hbodyRel⟩, hRc⟩ := lookupFun_pFunsRel hR hl
          have hbody' := (ihbody hRc (PropRel.blockS hbodyRel) (Compat.nil _)).1
          have hbody'' : Step D cenv' (decl'.params.zip argvals ++ bindZeros D decl'.rets) st1
              (.stmt (.block decl'.body)) (.sres Vend st2 .halt) := by
            rw [hpar, hret]; exact hbody'
          have hsub : Step D funs₂ V st (.expr (substExpr σ (.call fn args)))
              (.eres (.halt st2)) := by
            rw [substExpr]
            exact Step.callHalt hargs hl' (by rw [hpar]; exact hlen) hbody''
          cases hrhs with
          | subst => exact hsub
          | fold =>
              show Step D funs₂ V st (.expr (rhsExpr σ (.call fn args))) _
              rw [rhsExpr, substExpr, foldRhs_call]
              rw [substExpr] at hsub
              exact hsub
  | @callArgsHalt funs V st fn args st1 ha iha =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | expr hrhs =>
          refine ⟨?_, fun _ _ _ h => nomatch h⟩
          have hargs := (iha hR (PropRel.args) hc).1
          have hsub : Step D funs₂ V st (.expr (substExpr σ (.call fn args)))
              (.eres (.halt st1)) := by
            rw [substExpr]
            exact Step.callArgsHalt hargs
          cases hrhs with
          | subst => exact hsub
          | fold =>
              show Step D funs₂ V st (.expr (rhsExpr σ (.call fn args))) _
              rw [rhsExpr, substExpr, foldRhs_call]
              rw [substExpr] at hsub
              exact hsub
  | argsNil =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | args => exact ⟨Step.argsNil, fun _ _ _ h => nomatch h⟩
  | @argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | args =>
          refine ⟨?_, fun _ _ _ h => nomatch h⟩
          show Step D funs₂ V st (.args (substArgs σ (e :: rest))) _
          rw [substArgs]
          exact Step.argsCons ((ihrest hR (PropRel.args) hc).1)
            ((ihe hR (PropRel.expr .subst) hc).1)
  | @argsRestHalt funs V st e rest st1 hrest ihrest =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | args =>
          refine ⟨?_, fun _ _ _ h => nomatch h⟩
          show Step D funs₂ V st (.args (substArgs σ (e :: rest))) _
          rw [substArgs]
          exact Step.argsRestHalt ((ihrest hR (PropRel.args) hc).1)
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | args =>
          refine ⟨?_, fun _ _ _ h => nomatch h⟩
          show Step D funs₂ V st (.args (substArgs σ (e :: rest))) _
          rw [substArgs]
          exact Step.argsHeadHalt ((ihrest hR (PropRel.args) hc).1)
            ((ihe hR (PropRel.expr .subst) hc).1)
  | @funDef funs V st n ps rs b =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | funDefS hbody =>
          refine ⟨Step.funDef, ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1; subst h3
          intro _
          exact hc
  | @block funs V st body Vb stb o hb ihb =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | blockS hbodyRel =>
          have hstep := (ihb (List.Forall₂.cons (hbodyRel.hoist_scopeRel rfl rfl) hR)
            hbodyRel hc).1
          refine ⟨Step.block hstep, ?_⟩
          intro V' st' o' hres
          injection hres with h1 h2 h3
          subst h1
          intro _
          exact hc.of_frame (Step.env_frame (Step.block hb) rfl)
  | @letZero funs V st vars =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | letNoneS henv =>
          refine ⟨Step.letZero, ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1; subst h3
          intro _
          have hframe : EnvFrame vars V (bindZeros D vars ++ V) := by
            refine ⟨bindZeros D vars, V, rfl, rfl, ?_, fun _ _ => rfl⟩
            intro p hp
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
            exact hx
          cases henv with
          | skip => exact hc.of_frame hframe
          | zero hx =>
              subst hx
              intro p hp
              rcases List.mem_cons.mp hp with hp | hp
              · subst hp
                show VEnv.get (((_ : Ident), (evmWithExternal calls creates).zero) :: V) _
                  = some (litValue (.number 0))
                rw [VEnv.get_cons, if_pos rfl]
                rfl
              · exact hc.of_frame hframe _ hp
  | @letVal funs V st vars e vals st1 he hlen ihe =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | letSomeS hrhs henv =>
          next rhs' =>
          have heval : Step D funs₂ V st (.expr rhs') (.eres (.vals vals st1)) :=
            (ihe hR (PropRel.expr hrhs) hc).1
          refine ⟨Step.letVal heval hlen, ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1; subst h2; subst h3
          intro _
          have hframe : EnvFrame vars V (vars.zip vals ++ V) := by
            refine ⟨vars.zip vals, V, rfl, rfl, ?_, fun _ _ => rfl⟩
            intro p hp
            rcases p with ⟨a, b⟩
            exact (List.of_mem_zip hp).1
          cases henv with
          | skip => exact hc.of_frame hframe
          | create hx hcl =>
              subst hx
              have hv : ∃ v, vals = [v] := by
                cases vals with
                | nil => simp at hlen
                | cons v rest =>
                    cases rest with
                    | nil => exact ⟨v, rfl⟩
                    | cons _ _ => simp at hlen
              obtain ⟨v, rfl⟩ := hv
              next x r =>
              intro p hp
              rcases List.mem_cons.mp hp with hp | hp
              · subst hp
                cases r with
                | lit n =>
                    have hshape := classify_lit hcl
                    subst hshape
                    cases heval with
                    | lit =>
                        show VEnv.get ([x].zip [_] ++ V) x = _
                        simp only [List.zip_cons_cons, List.zip_nil_right,
                          List.cons_append, List.nil_append]
                        rw [VEnv.get_cons]
                        simp
                | var y =>
                    have hshape := classify_var hcl
                    subst hshape
                    cases heval with
                    | var hvy =>
                        refine ⟨v, ?_, ?_⟩
                        · show VEnv.get ([x].zip [v] ++ V) x = some v
                          simp only [List.zip_cons_cons, List.zip_nil_right,
                            List.cons_append, List.nil_append]
                          rw [VEnv.get_cons]
                          simp
                        · show VEnv.get ([x].zip [v] ++ V) y = some v
                          simp only [List.zip_cons_cons, List.zip_nil_right,
                            List.cons_append, List.nil_append]
                          rw [VEnv.get_cons]
                          by_cases hxy : x = y
                          · simp [hxy]
                          · simp only [hxy, if_false]
                            exact hvy
              · exact hc.of_frame hframe _ hp
  | @letHalt funs V st vars e st1 he ihe =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | letSomeS hrhs henv =>
          refine ⟨Step.letHalt ((ihe hR (PropRel.expr hrhs) hc).1), ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h3
          intro hno
          exact absurd hno (by simp)
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | assignS hrhs henv =>
          next rhs' =>
          have heval : Step D funs₂ V st (.expr rhs') (.eres (.vals vals st1)) :=
            (ihe hR (PropRel.expr hrhs) hc).1
          refine ⟨Step.assignVal heval hlen, ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1; subst h2; subst h3
          intro _
          have hframe : EnvFrame vars V (VEnv.setMany V vars vals) :=
            ⟨[], VEnv.setMany V vars vals, rfl, VEnv.setMany_keys V vars vals,
              fun p hp => absurd hp (List.not_mem_nil),
              fun x hx => VEnv.get_setMany_not_mem hx⟩
          cases henv with
          | skip => exact hc.of_frame hframe
          | refresh hx hbound hcl =>
              subst hx
              have hv : ∃ v, vals = [v] := by
                cases vals with
                | nil => simp at hlen
                | cons v rest =>
                    cases rest with
                    | nil => exact ⟨v, rfl⟩
                    | cons _ _ => simp at hlen
              obtain ⟨v, rfl⟩ := hv
              next x r =>
              have hxbound : (VEnv.get V x).isSome := by
                obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.mp hbound
                have := hc _ (mem_of_lookupEnv hr0)
                cases r0 with
                | lit n => rw [RhsHolds] at this; simp [this]
                | var y => obtain ⟨w, hw, _⟩ := this; simp [hw]
              have hset : VEnv.setMany V [x] [v] = VEnv.set V x v :=
                VEnv.setMany_singleton V x v
              intro p hp
              rcases List.mem_cons.mp hp with hp | hp
              · subst hp
                cases r with
                | lit n =>
                    have hshape := classify_lit hcl
                    subst hshape
                    cases heval with
                    | lit =>
                        show VEnv.get (VEnv.setMany V [x] [_]) x = _
                        rw [hset]
                        exact VEnv.get_set_self hxbound
                | var y =>
                    have hshape := classify_var hcl
                    subst hshape
                    cases heval with
                    | var hvy =>
                        refine ⟨v, ?_, ?_⟩
                        · show VEnv.get (VEnv.setMany V [x] [v]) x = some v
                          rw [hset]
                          exact VEnv.get_set_self hxbound
                        · show VEnv.get (VEnv.setMany V [x] [v]) y = some v
                          rw [hset]
                          by_cases hxy : y = x
                          · subst hxy
                            exact VEnv.get_set_self hxbound
                          · rw [VEnv.get_set_ne hxy]
                            exact hvy
              · have hpr := prune_not_hit hp
                have hbase := hc _ (List.mem_of_mem_filter hp)
                rcases p with ⟨z, rhs⟩
                have hzx : z ≠ x := by
                  intro hzx
                  subst hzx
                  cases rhs <;> simp [entryHits] at hpr
                cases rhs with
                | lit n =>
                    rw [RhsHolds] at hbase ⊢
                    rw [hset, VEnv.get_set_ne hzx]
                    exact hbase
                | var y =>
                    have hyx : y ≠ x := by
                      intro hyx
                      subst hyx
                      simp [entryHits] at hpr
                    obtain ⟨w, hwz, hwy⟩ := hbase
                    exact ⟨w, by rw [hset, VEnv.get_set_ne hzx]; exact hwz,
                      by rw [hset, VEnv.get_set_ne hyx]; exact hwy⟩
  | @assignHalt funs V st vars e st1 he ihe =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | assignS hrhs henv =>
          refine ⟨Step.assignHalt ((ihe hR (PropRel.expr hrhs) hc).1), ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h3
          intro hno
          exact absurd hno (by simp)
  | @exprStmt funs V st e st1 he ihe =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | exprStmtS =>
          refine ⟨Step.exprStmt ((ihe hR (PropRel.expr .subst) hc).1), ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1; subst h3
          intro _
          exact hc
  | @exprStmtHalt funs V st e st1 he ihe =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | exprStmtS =>
          refine ⟨Step.exprStmtHalt ((ihe hR (PropRel.expr .subst) hc).1), ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h3
          intro hno
          exact absurd hno (by simp)
  | @ifTrue funs V st c body cv st1 V2 st2 o hcv hnz hb ihc ihb =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | condS hbodyRel =>
          have hcond := (ihc hR (PropRel.expr .subst) hc).1
          have hstep := (ihb hR (PropRel.blockS hbodyRel) hc).1
          refine ⟨Step.ifTrue hcond hnz hstep, ?_⟩
          intro V' st' o' hres
          injection hres with h1 h2 h3
          subst h1
          intro _
          exact hc.of_frame (Step.env_frame (Step.ifTrue hcv hnz hb) rfl)
  | @ifFalse funs V st c body cv st1 hcv hz ihc =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | condS hbodyRel =>
          refine ⟨Step.ifFalse ((ihc hR (PropRel.expr .subst) hc).1) hz, ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1; subst h3
          intro _
          exact hc.restrict _
  | @ifHalt funs V st c body st1 hcv ihc =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | condS hbodyRel =>
          refine ⟨Step.ifHalt ((ihc hR (PropRel.expr .subst) hc).1), ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h3
          intro hno
          exact absurd hno (by simp)
  | @switchExec funs V st c cases dflt cv st1 V2 st2 o hcv hb ihc ihb =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | switchS hcases hdflt =>
          obtain ⟨σsel, hsel⟩ := hcases.selectRel hdflt cv
          have hcond := (ihc hR (PropRel.expr .subst) hc).1
          have hstep := (ihb hR (PropRel.blockS hsel) hc).1
          refine ⟨Step.switchExec hcond hstep, ?_⟩
          intro V' st' o' hres
          injection hres with h1 h2 h3
          subst h1
          intro _
          exact hc.of_frame (Step.env_frame (Step.switchExec hcv hb) rfl)
  | @switchHalt funs V st c cases dflt st1 hcv ihc =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | switchS hcases hdflt =>
          refine ⟨Step.switchHalt ((ihc hR (PropRel.expr .subst) hc).1), ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h3
          intro hno
          exact absurd hno (by simp)
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | forS hinitRel hσL hpostRel hbodyRel =>
          subst hσL
          have hRi := List.Forall₂.cons (hinitRel.hoist_scopeRel rfl rfl) hR
          obtain ⟨hinit', hcompatInit⟩ := ihinit hRi hinitRel hc
          have hcompVinit := hcompatInit Vinit stinit .normal rfl rfl
          have hloopRel := PropRel.loopL (c := c)
            (prune_idem _ (writeSetStmts post ++ writeSetStmts body)) hpostRel hbodyRel
          have hcompL := hcompVinit.restrict (writeSetStmts post ++ writeSetStmts body)
          obtain ⟨hloop', _⟩ := ihloop hRi hloopRel hcompL
          refine ⟨Step.forLoop hinit' hloop', ?_⟩
          intro V' st' o' hres
          injection hres with h1 h2 h3
          subst h1
          intro _
          exact hc.of_frame (Step.env_frame (Step.forLoop hinit hloop) rfl)
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | forS hinitRel hσL hpostRel hbodyRel =>
          have hRi := List.Forall₂.cons (hinitRel.hoist_scopeRel rfl rfl) hR
          obtain ⟨hinit', _⟩ := ihinit hRi hinitRel hc
          refine ⟨Step.forInitHalt hinit', ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h3
          intro hno
          exact absurd hno (by simp)
  | «break» =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | breakS =>
          refine ⟨Step.break, ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h3
          intro hno
          exact absurd hno (by simp)
  | «continue» =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | continueS =>
          refine ⟨Step.continue, ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h3
          intro hno
          exact absurd hno (by simp)
  | leave =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | leaveS =>
          refine ⟨Step.leave, ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h3
          intro hno
          exact absurd hno (by simp)
  | seqNil =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | nilSS =>
          refine ⟨Step.seqNil, ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1; subst h3
          intro _
          exact hc
  | @seqCons funs V st s rest V1 st1 V2 st2 o hs hrest ihs ihrest =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | consSS hsRel hrestRel =>
          obtain ⟨hs', hcompatS⟩ := ihs hR hsRel hc
          have hcompat1 := hcompatS V1 st1 .normal rfl rfl
          obtain ⟨hrest', hcompatRest⟩ := ihrest hR hrestRel hcompat1
          refine ⟨Step.seqCons hs' hrest', ?_⟩
          intro V' st' o' hres
          exact hcompatRest V' st' o' hres
  | @seqStop funs V st s rest V1 st1 o hs hne ihs =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | consSS hsRel hrestRel =>
          obtain ⟨hs', _⟩ := ihs hR hsRel hc
          refine ⟨Step.seqStop hs' hne, ?_⟩
          intro V' st' o' hres
          injection hres with h1 h2 h3
          subst h3
          intro hno
          exact absurd hno hne
  | @loopDone funs V st c post body cv st1 hcv hz ihc =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          refine ⟨Step.loopDone ((ihc hR (PropRel.expr .subst) hc).1) hz, ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1
          exact hc
  | @loopCondHalt funs V st c post body st1 hcv ihc =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          refine ⟨Step.loopCondHalt ((ihc hR (PropRel.expr .subst) hc).1), ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1
          exact hc
  | @loopStep funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o
      hcv hnz hb hob hp hloop ihc ihb ihp ihloop =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          have hcond := (ihc hR (PropRel.expr .subst) hc).1
          have hb' := (ihb hR (PropRel.blockS hbodyRel) hc).1
          have hcompVb : Compat Vb σ := by
            refine Compat.of_frame_stable hstable hc ?_
            exact (Step.env_frame hb rfl).mono
              (fun x hx => List.mem_append.mpr (Or.inr hx))
          have hp' := (ihp hR (PropRel.blockS hpostRel) hcompVb).1
          have hcompVp : Compat Vp σ := by
            refine Compat.of_frame_stable hstable hcompVb ?_
            exact (Step.env_frame hp rfl).mono
              (fun x hx => List.mem_append.mpr (Or.inl hx))
          obtain ⟨hloop', hcompatLoop⟩ := ihloop hR
            (PropRel.loopL hstable hpostRel hbodyRel) hcompVp
          refine ⟨Step.loopStep hcond hnz hb' hob hp' hloop', ?_⟩
          intro V' st' o' hres
          exact hcompatLoop V' st' o' hres
  | @loopPostHalt funs V st c post body cv st1 Vb stb ob Vp stp
      hcv hnz hb hob hp ihc ihb ihp =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          have hcond := (ihc hR (PropRel.expr .subst) hc).1
          have hb' := (ihb hR (PropRel.blockS hbodyRel) hc).1
          have hcompVb : Compat Vb σ := by
            refine Compat.of_frame_stable hstable hc ?_
            exact (Step.env_frame hb rfl).mono
              (fun x hx => List.mem_append.mpr (Or.inr hx))
          have hp' := (ihp hR (PropRel.blockS hpostRel) hcompVb).1
          refine ⟨Step.loopPostHalt hcond hnz hb' hob hp', ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1
          refine Compat.of_frame_stable hstable hcompVb ?_
          exact (Step.env_frame hp rfl).mono
            (fun x hx => List.mem_append.mpr (Or.inl hx))
  | @loopBreak funs V st c post body cv st1 Vb stb hcv hnz hb ihc ihb =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          have hcond := (ihc hR (PropRel.expr .subst) hc).1
          have hb' := (ihb hR (PropRel.blockS hbodyRel) hc).1
          refine ⟨Step.loopBreak hcond hnz hb', ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1
          refine Compat.of_frame_stable hstable hc ?_
          exact (Step.env_frame hb rfl).mono
            (fun x hx => List.mem_append.mpr (Or.inr hx))
  | @loopLeave funs V st c post body cv st1 Vb stb hcv hnz hb ihc ihb =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          have hcond := (ihc hR (PropRel.expr .subst) hc).1
          have hb' := (ihb hR (PropRel.blockS hbodyRel) hc).1
          refine ⟨Step.loopLeave hcond hnz hb', ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1
          refine Compat.of_frame_stable hstable hc ?_
          exact (Step.env_frame hb rfl).mono
            (fun x hx => List.mem_append.mpr (Or.inr hx))
  | @loopBodyHalt funs V st c post body cv st1 Vb stb hcv hnz hb ihc ihb =>
      intro funs₂ σ σ' pc' hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          have hcond := (ihc hR (PropRel.expr .subst) hc).1
          have hb' := (ihb hR (PropRel.blockS hbodyRel) hc).1
          refine ⟨Step.loopBodyHalt hcond hnz hb', ?_⟩
          intro V' st' o hres
          injection hres with h1 h2 h3
          subst h1
          refine Compat.of_frame_stable hstable hc ?_
          exact (Step.env_frame hb rfl).mono
            (fun x hx => List.mem_append.mpr (Or.inr hx))

/-! ### Shape inversion of related expressions (for the backward direction) -/

/-- A related expression is the substitution or the substitution-then-fold. -/
theorem RhsRel.eq_or_fold {σ : PEnv} {e t : Expr Op} (h : RhsRel σ e t) :
    t = substExpr σ e ∨ t = rhsExpr σ e := by
  cases h with
  | subst => exact Or.inl rfl
  | fold => exact Or.inr rfl

theorem foldRhs_builtin_nolits {op : Op} {args : List (Expr Op)}
    (h : asLits args = none) : foldRhs (.builtin op args) = .builtin op args := by
  simp only [foldRhs, h]

theorem foldRhs_builtin_nofold {op : Op} {args : List (Expr Op)} {lits : List Literal}
    (hl : asLits args = some lits) (h : pureFold op lits = none) :
    foldRhs (.builtin op args) = .builtin op args := by
  simp only [foldRhs, hl, h]

theorem foldRhs_builtin_fold {op : Op} {args : List (Expr Op)} {lits : List Literal}
    {l : Literal} (hl : asLits args = some lits) (h : pureFold op lits = some l) :
    foldRhs (.builtin op args) = .lit l := by
  simp only [foldRhs, hl, h]

/-- A related expression that is a builtin call comes from the same builtin
with substituted arguments (folding never *produces* a builtin from another
shape). -/
theorem RhsRel.builtin_inv {σ : PEnv} {e : Expr Op} {op : Op} {es' : List (Expr Op)}
    (h : RhsRel σ e (.builtin op es')) :
    ∃ args, e = .builtin op args ∧ es' = substArgs σ args := by
  rcases h.eq_or_fold with ht | ht
  · cases e with
    | lit l => rw [substExpr] at ht; cases ht
    | var x =>
        rw [substExpr] at ht
        cases hlook : lookupEnv σ x with
        | none => rw [hlook] at ht; cases ht
        | some r => rw [hlook] at ht; cases r <;> simp [PRhs.toExpr] at ht
    | builtin op0 args =>
        rw [substExpr] at ht
        injection ht with h1 h2
        exact ⟨args, by rw [h1], h2⟩
    | call f args => rw [substExpr] at ht; cases ht
  · cases e with
    | lit l => rw [rhsExpr] at ht; simp only [substExpr, foldRhs_lit] at ht; cases ht
    | var x =>
        rw [rhsExpr, foldRhs_substVar] at ht
        rw [substExpr] at ht
        cases hlook : lookupEnv σ x with
        | none => rw [hlook] at ht; cases ht
        | some r => rw [hlook] at ht; cases r <;> simp [PRhs.toExpr] at ht
    | builtin op0 args =>
        rw [rhsExpr, substExpr] at ht
        cases hlits : asLits (substArgs σ args) with
        | none =>
            rw [foldRhs_builtin_nolits hlits] at ht
            injection ht with h1 h2
            exact ⟨args, by rw [h1], h2⟩
        | some lits =>
            cases hfold : pureFold op0 lits with
            | none =>
                rw [foldRhs_builtin_nofold hlits hfold] at ht
                injection ht with h1 h2
                exact ⟨args, by rw [h1], h2⟩
            | some l =>
                rw [foldRhs_builtin_fold hlits hfold] at ht
                cases ht
    | call f args => rw [rhsExpr, substExpr, foldRhs_call] at ht; cases ht

/-- A related expression that is a user call comes from the same call with
substituted arguments. -/
theorem RhsRel.call_inv {σ : PEnv} {e : Expr Op} {f : Ident} {es' : List (Expr Op)}
    (h : RhsRel σ e (.call f es')) :
    ∃ args, e = .call f args ∧ es' = substArgs σ args := by
  rcases h.eq_or_fold with ht | ht
  · cases e with
    | lit l => rw [substExpr] at ht; cases ht
    | var x =>
        rw [substExpr] at ht
        cases hlook : lookupEnv σ x with
        | none => rw [hlook] at ht; cases ht
        | some r => rw [hlook] at ht; cases r <;> simp [PRhs.toExpr] at ht
    | builtin op0 args => rw [substExpr] at ht; cases ht
    | call f0 args =>
        rw [substExpr] at ht
        injection ht with h1 h2
        exact ⟨args, by rw [h1], h2⟩
  · cases e with
    | lit l => rw [rhsExpr] at ht; simp only [substExpr, foldRhs_lit] at ht; cases ht
    | var x =>
        rw [rhsExpr, foldRhs_substVar] at ht
        rw [substExpr] at ht
        cases hlook : lookupEnv σ x with
        | none => rw [hlook] at ht; cases ht
        | some r => rw [hlook] at ht; cases r <;> simp [PRhs.toExpr] at ht
    | builtin op0 args =>
        rw [rhsExpr, substExpr] at ht
        cases hlits : asLits (substArgs σ args) with
        | none => rw [foldRhs_builtin_nolits hlits] at ht; cases ht
        | some lits =>
            cases hfold : pureFold op0 lits with
            | none => rw [foldRhs_builtin_nofold hlits hfold] at ht; cases ht
            | some l => rw [foldRhs_builtin_fold hlits hfold] at ht; cases ht
    | call f0 args =>
        rw [rhsExpr, substExpr, foldRhs_call] at ht
        injection ht with h1 h2
        exact ⟨args, by rw [h1], h2⟩

/-- A related expression that is a variable read comes from a variable read
whose substitution it is. -/
theorem RhsRel.var_inv {σ : PEnv} {e : Expr Op} {y : Ident}
    (h : RhsRel σ e (.var y)) :
    ∃ x, e = .var x ∧ substExpr σ (.var x) = .var y := by
  rcases h.eq_or_fold with ht | ht
  · cases e with
    | lit l => rw [substExpr] at ht; cases ht
    | var x => exact ⟨x, rfl, ht.symm⟩
    | builtin op0 args => rw [substExpr] at ht; cases ht
    | call f args => rw [substExpr] at ht; cases ht
  · cases e with
    | lit l => rw [rhsExpr] at ht; simp only [substExpr, foldRhs_lit] at ht; cases ht
    | var x =>
        rw [rhsExpr, foldRhs_substVar] at ht
        exact ⟨x, rfl, ht.symm⟩
    | builtin op0 args =>
        rw [rhsExpr, substExpr] at ht
        cases hlits : asLits (substArgs σ args) with
        | none => rw [foldRhs_builtin_nolits hlits] at ht; cases ht
        | some lits =>
            cases hfold : pureFold op0 lits with
            | none => rw [foldRhs_builtin_nofold hlits hfold] at ht; cases ht
            | some l => rw [foldRhs_builtin_fold hlits hfold] at ht; cases ht
    | call f args => rw [rhsExpr, substExpr, foldRhs_call] at ht; cases ht

/-- A related expression that is a literal: the same literal, a substituted
tracked read, or a folded all-literal builtin. -/
theorem RhsRel.lit_inv {σ : PEnv} {e : Expr Op} {l : Literal}
    (h : RhsRel σ e (.lit l)) :
    e = .lit l ∨
    (∃ x, e = .var x ∧ substExpr σ (.var x) = .lit l) ∨
    (∃ op args lits w, e = .builtin op args ∧
      asLits (substArgs σ args) = some lits ∧
      pureFn op (lits.map litValue) = some w ∧ l = .number w.toNat) := by
  rcases h.eq_or_fold with ht | ht
  · cases e with
    | lit l0 =>
        rw [substExpr] at ht
        injection ht with h1
        exact Or.inl (by rw [h1])
    | var x => exact Or.inr (Or.inl ⟨x, rfl, ht.symm⟩)
    | builtin op0 args => rw [substExpr] at ht; cases ht
    | call f args => rw [substExpr] at ht; cases ht
  · cases e with
    | lit l0 =>
        rw [rhsExpr] at ht
        simp only [substExpr, foldRhs_lit] at ht
        injection ht with h1
        exact Or.inl (by rw [h1])
    | var x =>
        rw [rhsExpr, foldRhs_substVar] at ht
        exact Or.inr (Or.inl ⟨x, rfl, ht.symm⟩)
    | builtin op0 args =>
        rw [rhsExpr, substExpr] at ht
        cases hlits : asLits (substArgs σ args) with
        | none => rw [foldRhs_builtin_nolits hlits] at ht; cases ht
        | some lits =>
            cases hfold : pureFold op0 lits with
            | none => rw [foldRhs_builtin_nofold hlits hfold] at ht; cases ht
            | some l0 =>
                rw [foldRhs_builtin_fold hlits hfold] at ht
                injection ht with h1
                subst h1
                rw [pureFold, Option.map_eq_some_iff] at hfold
                obtain ⟨w, hw, rfl⟩ := hfold
                exact Or.inr (Or.inr ⟨op0, args, lits, w, rfl, hlits, hw, rfl⟩)
    | call f args => rw [rhsExpr, substExpr, foldRhs_call] at ht; cases ht

/-- Inversion of an argument-list relation target. -/
theorem PropRel.args_inv {σ σ' : PEnv} {pc : PCode Op} {es' : List (Expr Op)}
    (h : PropRel σ σ' pc (.args es')) :
    ∃ es, pc = .args es ∧ σ' = σ ∧ es' = substArgs σ es := by
  cases h with
  | args => exact ⟨_, rfl, rfl, rfl⟩

/-- **Backward simulation.** A derivation of the propagated program transports
back to a derivation of the source with the same result. Together with
`prop_fwd` this closes the pointwise iff. -/
theorem prop_bwd {funs₂ : FunEnv D} {V : VEnv D} {st : EvmState}
    {code' : Code Op} {res : Res D} (h : Step D funs₂ V st code' res) :
    ∀ {funs₁ : FunEnv D} {σ σ' : PEnv} {pc : PCode Op},
      PFunsRel funs₁ funs₂ → PropRel σ σ' pc (toPCode code') → Compat V σ →
      Step D funs₁ V st (ofPCode pc) res := by
  induction h with
  | @lit funs V st l =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | expr hrhs =>
          rcases hrhs.lit_inv with rfl | ⟨x, rfl, hsub⟩ |
            ⟨op, args, lits, w, rfl, hlits, hw, rfl⟩
          · exact Step.lit
          · refine substVar_eval_bwd hc ?_
            rw [hsub]
            exact Step.lit
          · show Step D funs₁ V st (.expr (.builtin op args)) _
            have hargs : Step D funs₁ V st (.args args)
                (.eres (.vals (lits.map litValue) st)) :=
              substArgs_lits_eval hc funs₁ st (asLits_map hlits)
            have hstep := Step.builtinOk hargs
              (pureFn_builtin (calls := calls) (creates := creates) hw st)
            have hlv : litValue (.number w.toNat) = w := litValue_number_toNat w
            rw [← hlv] at hstep
            exact hstep
  | @var funs V st x0 v hv =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | expr hrhs =>
          obtain ⟨x, rfl, hsub⟩ := hrhs.var_inv
          refine substVar_eval_bwd hc ?_
          rw [hsub]
          exact Step.var hv
  | @builtinOk funs V st op args' argvals st1 rets st2 ha hb iha =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | expr hrhs =>
          obtain ⟨args, rfl, rfl⟩ := hrhs.builtin_inv
          exact Step.builtinOk (iha hR (PropRel.args) hc) hb
  | @builtinHalt funs V st op args' argvals st1 st2 ha hb iha =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | expr hrhs =>
          obtain ⟨args, rfl, rfl⟩ := hrhs.builtin_inv
          exact Step.builtinHalt (iha hR (PropRel.args) hc) hb
  | @builtinArgsHalt funs V st op args' st1 ha iha =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | expr hrhs =>
          obtain ⟨args, rfl, rfl⟩ := hrhs.builtin_inv
          exact Step.builtinArgsHalt (iha hR (PropRel.args) hc)
  | @callOk funs V st fn args' argvals st1 decl' cenv' Vend st2 o
      ha hl hlen hbody ho iha ihbody =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | expr hrhs =>
          obtain ⟨args, rfl, rfl⟩ := hrhs.call_inv
          obtain ⟨decl, cenv, hl0, hpar, hret, ⟨σb, hbodyRel⟩, hRc⟩ :=
            lookupFun_pFunsRel_bwd hR hl
          have hargs := iha hR (PropRel.args) hc
          have hbody0 : Step D cenv (decl.params.zip argvals ++ bindZeros D decl.rets) st1
              (.stmt (.block decl.body)) (.sres Vend st2 o) := by
            have hib := ihbody hRc (PropRel.blockS hbodyRel) (Compat.nil _)
            rw [hpar, hret] at hib
            exact hib
          have hlen0 : argvals.length = decl.params.length := by
            rw [← hpar]; exact hlen
          have hres := Step.callOk hargs hl0 hlen0 hbody0 ho
          rw [← hret] at hres
          exact hres
  | @callHalt funs V st fn args' argvals st1 decl' cenv' Vend st2
      ha hl hlen hbody iha ihbody =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | expr hrhs =>
          obtain ⟨args, rfl, rfl⟩ := hrhs.call_inv
          obtain ⟨decl, cenv, hl0, hpar, hret, ⟨σb, hbodyRel⟩, hRc⟩ :=
            lookupFun_pFunsRel_bwd hR hl
          have hargs := iha hR (PropRel.args) hc
          have hbody0 : Step D cenv (decl.params.zip argvals ++ bindZeros D decl.rets) st1
              (.stmt (.block decl.body)) (.sres Vend st2 .halt) := by
            have hib := ihbody hRc (PropRel.blockS hbodyRel) (Compat.nil _)
            rw [hpar, hret] at hib
            exact hib
          have hlen0 : argvals.length = decl.params.length := by
            rw [← hpar]; exact hlen
          exact Step.callHalt hargs hl0 hlen0 hbody0
  | @callArgsHalt funs V st fn args' st1 ha iha =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | expr hrhs =>
          obtain ⟨args, rfl, rfl⟩ := hrhs.call_inv
          exact Step.callArgsHalt (iha hR (PropRel.args) hc)
  | @argsNil funs V st =>
      intro funs₁ σ σ' pc hR hrel hc
      obtain ⟨es, rfl, rfl, heq⟩ := hrel.args_inv
      cases es with
      | nil => exact Step.argsNil
      | cons e0 rest0 => rw [substArgs] at heq; cases heq
  | @argsCons funs V st e' rest' restvals st1 v st2 hrest he ihrest ihe =>
      intro funs₁ σ σ' pc hR hrel hc
      obtain ⟨es, rfl, rfl, heq⟩ := hrel.args_inv
      cases es with
      | nil => rw [substArgs] at heq; cases heq
      | cons e0 rest0 =>
          rw [substArgs] at heq
          injection heq with h1 h2
          subst h1; subst h2
          exact Step.argsCons (ihrest hR (PropRel.args) hc)
            (ihe hR (PropRel.expr .subst) hc)
  | @argsRestHalt funs V st e' rest' st1 hrest ihrest =>
      intro funs₁ σ σ' pc hR hrel hc
      obtain ⟨es, rfl, rfl, heq⟩ := hrel.args_inv
      cases es with
      | nil => rw [substArgs] at heq; cases heq
      | cons e0 rest0 =>
          rw [substArgs] at heq
          injection heq with h1 h2
          subst h1; subst h2
          exact Step.argsRestHalt (ihrest hR (PropRel.args) hc)
  | @argsHeadHalt funs V st e' rest' restvals st1 st2 hrest he ihrest ihe =>
      intro funs₁ σ σ' pc hR hrel hc
      obtain ⟨es, rfl, rfl, heq⟩ := hrel.args_inv
      cases es with
      | nil => rw [substArgs] at heq; cases heq
      | cons e0 rest0 =>
          rw [substArgs] at heq
          injection heq with h1 h2
          subst h1; subst h2
          exact Step.argsHeadHalt (ihrest hR (PropRel.args) hc)
            (ihe hR (PropRel.expr .subst) hc)
  | @funDef funs V st n ps rs b' =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | funDefS hbody => exact Step.funDef
  | @block funs V st body' Vb stb o hb ihb =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | blockS hbodyRel =>
          exact Step.block (ihb
            (List.Forall₂.cons (hbodyRel.hoist_scopeRel rfl rfl) hR) hbodyRel hc)
  | @letZero funs V st vars =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | letNoneS henv => exact Step.letZero
  | @letVal funs V st vars rhs' vals st1 he hlen ihe =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | letSomeS hrhs henv =>
          exact Step.letVal (ihe hR (PropRel.expr hrhs) hc) hlen
  | @letHalt funs V st vars rhs' st1 he ihe =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | letSomeS hrhs henv =>
          exact Step.letHalt (ihe hR (PropRel.expr hrhs) hc)
  | @assignVal funs V st vars rhs' vals st1 he hlen ihe =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | assignS hrhs henv =>
          exact Step.assignVal (ihe hR (PropRel.expr hrhs) hc) hlen
  | @assignHalt funs V st vars rhs' st1 he ihe =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | assignS hrhs henv =>
          exact Step.assignHalt (ihe hR (PropRel.expr hrhs) hc)
  | @exprStmt funs V st e' st1 he ihe =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | exprStmtS => exact Step.exprStmt (ihe hR (PropRel.expr .subst) hc)
  | @exprStmtHalt funs V st e' st1 he ihe =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | exprStmtS => exact Step.exprStmtHalt (ihe hR (PropRel.expr .subst) hc)
  | @ifTrue funs V st c0 body' cv st1 V2 st2 o hcv hnz hb ihc ihb =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | condS hbodyRel =>
          exact Step.ifTrue (ihc hR (PropRel.expr .subst) hc) hnz
            (ihb hR (PropRel.blockS hbodyRel) hc)
  | @ifFalse funs V st c0 body' cv st1 hcv hz ihc =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | condS hbodyRel =>
          exact Step.ifFalse (ihc hR (PropRel.expr .subst) hc) hz
  | @ifHalt funs V st c0 body' st1 hcv ihc =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | condS hbodyRel =>
          exact Step.ifHalt (ihc hR (PropRel.expr .subst) hc)
  | @switchExec funs V st c0 cases' dflt' cv st1 V2 st2 o hcv hb ihc ihb =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | switchS hcases hdflt =>
          obtain ⟨σsel, hsel⟩ := hcases.selectRel hdflt cv
          exact Step.switchExec (ihc hR (PropRel.expr .subst) hc)
            (ihb hR (PropRel.blockS hsel) hc)
  | @switchHalt funs V st c0 cases' dflt' st1 hcv ihc =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | switchS hcases hdflt =>
          exact Step.switchHalt (ihc hR (PropRel.expr .subst) hc)
  | @forLoop funs V st init' c0 post' body' Vinit stinit Vend stend o
      hinit hloop ihinit ihloop =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | forS hinitRel hσL hpostRel hbodyRel =>
          subst hσL
          have hRi := List.Forall₂.cons (hinitRel.hoist_scopeRel rfl rfl) hR
          have hinit0 := ihinit hRi hinitRel hc
          have hcomp := (prop_fwd hinit0 hRi hinitRel hc).2 Vinit stinit .normal rfl rfl
          exact Step.forLoop hinit0 (ihloop hRi
            (PropRel.loopL (prune_idem _ _) hpostRel hbodyRel) (hcomp.restrict _))
  | @forInitHalt funs V st init' c0 post' body' Vinit stinit hinit ihinit =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | forS hinitRel hσL hpostRel hbodyRel =>
          have hRi := List.Forall₂.cons (hinitRel.hoist_scopeRel rfl rfl) hR
          exact Step.forInitHalt (ihinit hRi hinitRel hc)
  | «break» =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | breakS => exact Step.break
  | «continue» =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | continueS => exact Step.continue
  | leave =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | leaveS => exact Step.leave
  | seqNil =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | nilSS => exact Step.seqNil
  | @seqCons funs V st s' rest' V1 st1 V2 st2 o hs hrest ihs ihrest =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | consSS hsRel hrestRel =>
          have hs0 := ihs hR hsRel hc
          have hcomp1 := (prop_fwd hs0 hR hsRel hc).2 V1 st1 .normal rfl rfl
          exact Step.seqCons hs0 (ihrest hR hrestRel hcomp1)
  | @seqStop funs V st s' rest' V1 st1 o hs hne ihs =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | consSS hsRel hrestRel =>
          exact Step.seqStop (ihs hR hsRel hc) hne
  | @loopDone funs V st c0 post' body' cv st1 hcv hz ihc =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          exact Step.loopDone (ihc hR (PropRel.expr .subst) hc) hz
  | @loopCondHalt funs V st c0 post' body' st1 hcv ihc =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          exact Step.loopCondHalt (ihc hR (PropRel.expr .subst) hc)
  | @loopStep funs V st c0 post' body' cv st1 Vb stb ob Vp stp Vend stend o
      hcv hnz hb hob hp hloop ihc ihb ihp ihloop =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          have hcond := ihc hR (PropRel.expr .subst) hc
          have hb0 := ihb hR (PropRel.blockS hbodyRel) hc
          have hcompVb : Compat Vb σ := by
            refine Compat.of_frame_stable hstable hc ?_
            exact (Step.env_frame hb0 rfl).mono
              (fun x hx => List.mem_append.mpr (Or.inr hx))
          have hp0 := ihp hR (PropRel.blockS hpostRel) hcompVb
          have hcompVp : Compat Vp σ := by
            refine Compat.of_frame_stable hstable hcompVb ?_
            exact (Step.env_frame hp0 rfl).mono
              (fun x hx => List.mem_append.mpr (Or.inl hx))
          exact Step.loopStep hcond hnz hb0 hob hp0
            (ihloop hR (PropRel.loopL hstable hpostRel hbodyRel) hcompVp)
  | @loopPostHalt funs V st c0 post' body' cv st1 Vb stb ob Vp stp
      hcv hnz hb hob hp ihc ihb ihp =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          have hcond := ihc hR (PropRel.expr .subst) hc
          have hb0 := ihb hR (PropRel.blockS hbodyRel) hc
          have hcompVb : Compat Vb σ := by
            refine Compat.of_frame_stable hstable hc ?_
            exact (Step.env_frame hb0 rfl).mono
              (fun x hx => List.mem_append.mpr (Or.inr hx))
          exact Step.loopPostHalt hcond hnz hb0 hob
            (ihp hR (PropRel.blockS hpostRel) hcompVb)
  | @loopBreak funs V st c0 post' body' cv st1 Vb stb hcv hnz hb ihc ihb =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          exact Step.loopBreak (ihc hR (PropRel.expr .subst) hc) hnz
            (ihb hR (PropRel.blockS hbodyRel) hc)
  | @loopLeave funs V st c0 post' body' cv st1 Vb stb hcv hnz hb ihc ihb =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          exact Step.loopLeave (ihc hR (PropRel.expr .subst) hc) hnz
            (ihb hR (PropRel.blockS hbodyRel) hc)
  | @loopBodyHalt funs V st c0 post' body' cv st1 Vb stb hcv hnz hb ihc ihb =>
      intro funs₁ σ σ' pc hR hrel hc
      cases hrel with
      | loopL hstable hpostRel hbodyRel =>
          exact Step.loopBodyHalt (ihc hR (PropRel.expr .subst) hc) hnz
            (ihb hR (PropRel.blockS hbodyRel) hc)

/-! ### The pass -/

/-- Related blocks are semantically equivalent: the two simulations, packaged
through the hoisted-scope extension of `PFunsRel`. -/
theorem PropRel.equivBlock {σ' : PEnv} {b b' : Block Op}
    (hrel : PropRel [] σ' (.stmts b) (.stmts b')) :
    EquivBlock D b b' := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | block hb =>
        refine Step.block ?_
        exact (prop_fwd hb (List.Forall₂.cons (hrel.hoist_scopeRel rfl rfl)
          (PFunsRel.refl funs)) hrel (Compat.nil V)).1
  · intro h
    cases h with
    | block hb =>
        refine Step.block ?_
        exact prop_bwd hb (List.Forall₂.cons (hrel.hoist_scopeRel rfl rfl)
          (PFunsRel.refl funs)) hrel (Compat.nil V)

/-- The **Propagate pass**: constant + copy propagation with binding-preserving
substitution, assignment refresh, zero-init tracking, and rhs folding — bundled
with its soundness proof. -/
def propagate : Pass D where
  run := propagateBlock
  sound := fun b => PropRel.equivBlock (propStmts_rel (copyGate 0 b) [] b)

@[simp] theorem propagate_run (b : Block Op) :
    (propagate (calls := calls) (creates := creates)).run b =
      (propStmts (copyGate 0 b) [] b).1 := rfl

/-! ### Regression examples (checked at build time) -/

-- Constant propagation feeds folding: `let a := 1  let b := add(a, 1)` chains.
example : (propStmts false [] [.letDecl ["a"] (some (.lit (.number 1))),
    .letDecl ["b"] (some (.builtin .add [.var "a", .lit (.number 1)])),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "b"])]).1
  = [.letDecl ["a"] (some (.lit (.number 1))),
     .letDecl ["b"] (some (.lit (.number 2))),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 2)])] := rfl
-- Copy entries are gate-controlled (DUP16 depth): a bare copy stays
-- untouched when the gate is off...
example : (propStmts false [] [.letDecl ["y"] (some (.var "x")),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "y"])]).1
  = [.letDecl ["y"] (some (.var "x")),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "y"])] := rfl
-- ...and is substituted (binding preserved) when it is on.
example : (propStmts true [] [.letDecl ["y"] (some (.var "x")),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "y"])]).1
  = [.letDecl ["y"] (some (.var "x")),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])] := rfl
-- ...but copy chains still collapse through tracked literals (depth-safe).
example : (propStmts false [] [.letDecl ["x"] (some (.lit (.number 7))),
    .letDecl ["y"] (some (.var "x")),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "y"])]).1
  = [.letDecl ["x"] (some (.lit (.number 7))),
     .letDecl ["y"] (some (.lit (.number 7))),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 7)])] := rfl
-- Assignment refresh: reassigned literals are tracked (`multi_reassign`).
example : (propStmts false [] [.letDecl ["a"] (some (.lit (.number 1))),
    .assign ["a"] (.lit (.number 2)),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "a"])]).1
  = [.letDecl ["a"] (some (.lit (.number 1))),
     .assign ["a"] (.lit (.number 2)),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 2)])] := rfl
-- Refresh kills stale copies: `y ↦ x` must die when `x` is refreshed.
example : (propStmts false [] [.letDecl ["x"] (some (.lit (.number 1))),
    .letDecl ["y"] (some (.var "x")),
    .assign ["x"] (.lit (.number 2)),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "y"])]).1
  = [.letDecl ["x"] (some (.lit (.number 1))),
     .letDecl ["y"] (some (.lit (.number 1))),
     .assign ["x"] (.lit (.number 2)),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- Uninitialized `let` shadows: `let x := 1  let x  use x` must read 0.
example : (propStmts false [] [.letDecl ["x"] (some (.lit (.number 1))),
    .letDecl ["x"] none,
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])]).1
  = [.letDecl ["x"] (some (.lit (.number 1))),
     .letDecl ["x"] none,
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 0)])] := rfl
-- A variable assigned inside a loop body is NOT propagated into the loop.
example : (propStmts false [] [.letDecl ["i"] (some (.lit (.number 0))),
    .forLoop [] (.builtin .lt [.var "i", .lit (.number 10)])
      [.assign ["i"] (.builtin .add [.var "i", .lit (.number 1)])]
      [.exprStmt (.builtin .sstore [.var "i", .var "i"])]]).1
  = [.letDecl ["i"] (some (.lit (.number 0))),
     .forLoop [] (.builtin .lt [.var "i", .lit (.number 10)])
       [.assign ["i"] (.builtin .add [.var "i", .lit (.number 1)])]
       [.exprStmt (.builtin .sstore [.var "i", .var "i"])]] := rfl
-- funDef bodies restart at σ = [] (no caller-variable capture).
example : (propStmts false [] [.letDecl ["x"] (some (.lit (.number 5))),
    .funDef "f" [] ["r"] [.assign ["r"] (.var "x")]]).1
  = [.letDecl ["x"] (some (.lit (.number 5))),
     .funDef "f" [] ["r"] [.assign ["r"] (.var "x")]] := rfl

end YulEvmCompiler.Optimizer
