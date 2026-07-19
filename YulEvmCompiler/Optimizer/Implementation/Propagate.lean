import YulEvmCompiler.Optimizer.Spec.Pass
import YulEvmCompiler.Optimizer.Implementation.Simplify
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

/-- The tracked environment after `let xs := rhs'`: prune the shadowed names,
then track a singleton whose rewritten rhs is classifiable. -/
def letEnv (σ : PEnv) (xs : List Ident) (rhs' : Expr Op) : PEnv :=
  match xs, classify rhs' with
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
def assignEnv (σ : PEnv) (xs : List Ident) (rhs' : Expr Op) : PEnv :=
  match xs, classify rhs' with
  | [x], some r =>
      if (lookupEnv σ x).isSome then (x, r) :: prune σ [x] else prune σ xs
  | _, _ => prune σ xs

mutual

/-- Propagate through one statement, returning the rewritten statement and the
tracked environment for the statements that follow it. -/
def propStmt (σ : PEnv) : Stmt Op → Stmt Op × PEnv
  | .block body =>
      (.block (propStmts σ body).1, prune σ (writeSetStmts body))
  | .funDef n ps rs body =>
      (.funDef n ps rs (propStmts [] body).1, σ)
  | .letDecl xs none =>
      (.letDecl xs none, letZeroEnv σ xs)
  | .letDecl xs (some e) =>
      let r := rhsExpr σ e
      (.letDecl xs (some r), letEnv σ xs r)
  | .assign xs e =>
      let r := rhsExpr σ e
      (.assign xs r, assignEnv σ xs r)
  | .cond c body =>
      (.cond (substExpr σ c) (propStmts σ body).1, prune σ (writeSetStmts body))
  | .switch c cases dflt =>
      (.switch (substExpr σ c) (propCases σ cases) (propDflt σ dflt),
        prune σ (writeSetCases cases ++ writeSetDflt dflt))
  | .forLoop init c post body =>
      let pinit := propStmts σ init
      let σL := prune pinit.2 (writeSetStmts post ++ writeSetStmts body)
      (.forLoop pinit.1 (substExpr σL c) (propStmts σL post).1 (propStmts σL body).1,
        prune σ (writeSetStmts init ++ writeSetStmts post ++ writeSetStmts body))
  | .exprStmt e => (.exprStmt (substExpr σ e), σ)
  | .break => (.break, σ)
  | .continue => (.continue, σ)
  | .leave => (.leave, σ)

/-- Propagate through a statement sequence, threading the environment. -/
def propStmts (σ : PEnv) : List (Stmt Op) → List (Stmt Op) × PEnv
  | [] => ([], σ)
  | s :: rest =>
      let ps := propStmt σ s
      let prest := propStmts ps.2 rest
      (ps.1 :: prest.1, prest.2)

/-- Propagate through each `switch` case body (labels preserved). -/
def propCases (σ : PEnv) : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, (propStmts σ b).1) :: propCases σ rest

/-- Propagate through a `switch`'s optional default. -/
def propDflt (σ : PEnv) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some ((propStmts σ b).1)

end

/-- The pass entry point: propagate through a top-level block. -/
def propagateBlock (b : Block Op) : Block Op := (propStmts [] b).1

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

/-- `letEnv` is a valid `LetEnvRel` choice. -/
theorem letEnv_rel (σ : PEnv) (xs : List Ident) (rhs' : Expr Op) :
    LetEnvRel σ xs rhs' (letEnv σ xs rhs') := by
  unfold letEnv
  split
  · next x r hcl => exact .create rfl hcl
  · exact .skip

/-- `letZeroEnv` is a valid `LetZeroEnvRel` choice. -/
theorem letZeroEnv_rel (σ : PEnv) (xs : List Ident) :
    LetZeroEnvRel σ xs (letZeroEnv σ xs) := by
  unfold letZeroEnv
  split
  · exact .zero rfl
  · exact .skip

/-- `assignEnv` is a valid `AssignEnvRel` choice. -/
theorem assignEnv_rel (σ : PEnv) (xs : List Ident) (rhs' : Expr Op) :
    AssignEnvRel σ xs rhs' (assignEnv σ xs rhs') := by
  unfold assignEnv
  split
  · next x r hcl =>
      split
      · next hb => exact .refresh rfl hb hcl
      · exact .skip
  · exact .skip

mutual

/-- The statement transform inhabits the relation. -/
theorem propStmt_rel (σ : PEnv) : ∀ s : Stmt Op,
    PropRel σ (propStmt σ s).2
      (.stmt s) (.stmt (propStmt σ s).1)
  | .block body => .blockS (propStmts_rel σ body)
  | .funDef _ _ _ body => .funDefS (propStmts_rel [] body)
  | .letDecl xs none => .letNoneS (letZeroEnv_rel σ xs)
  | .letDecl xs (some e) => .letSomeS (.fold) (letEnv_rel σ xs (rhsExpr σ e))
  | .assign xs e => .assignS (.fold) (assignEnv_rel σ xs (rhsExpr σ e))
  | .cond _ body => .condS (propStmts_rel σ body)
  | .switch _ cases dflt => .switchS (propCases_rel σ cases) (propDflt_rel σ dflt)
  | .forLoop init _ post body =>
      .forS (propStmts_rel σ init) rfl
        (propStmts_rel _ post) (propStmts_rel _ body)
  | .exprStmt _ => .exprStmtS
  | .break => .breakS
  | .continue => .continueS
  | .leave => .leaveS

/-- The sequence transform inhabits the relation. -/
theorem propStmts_rel (σ : PEnv) : ∀ ss : List (Stmt Op),
    PropRel σ (propStmts σ ss).2
      (.stmts ss) (.stmts (propStmts σ ss).1)
  | [] => .nilSS
  | s :: rest => .consSS (propStmt_rel σ s) (propStmts_rel (propStmt σ s).2 rest)

/-- The case-list transform inhabits the relation. -/
theorem propCases_rel (σ : PEnv) : ∀ cs : List (Literal × Block Op),
    PropRel σ σ
      (.cases cs) (.cases (propCases σ cs))
  | [] => .casesNil
  | (_, b) :: rest => .casesCons (propStmts_rel σ b) (propCases_rel σ rest)

/-- The default transform inhabits the relation. -/
theorem propDflt_rel (σ : PEnv) : ∀ d : Option (Block Op),
    PropRel σ σ
      (.odflt d) (.odflt (propDflt σ d))
  | none => .odfltNone
  | some b => .odfltSome (propStmts_rel σ b)

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

/-- In-place update preserves the key sequence. -/
theorem VEnv.set_keys (V : VEnv D) (x : Ident) (v : U256) :
    (VEnv.set V x v).map Prod.fst = V.map Prod.fst := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      rw [VEnv.set]
      split
      · next h => simp [← h]
      · simp [ih]

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

/-- One `foldl` of updates preserves the key sequence. -/
private theorem foldl_set_keys (l : List (Ident × U256)) (V : VEnv D) :
    (l.foldl (fun acc p => VEnv.set acc p.1 p.2) V).map Prod.fst = V.map Prod.fst := by
  induction l generalizing V with
  | nil => rfl
  | cons p rest ih => rw [List.foldl_cons, ih, VEnv.set_keys]

/-- Multi-update preserves the key sequence. -/
theorem VEnv.setMany_keys (V : VEnv D) (xs : List Ident) (vs : List U256) :
    (VEnv.setMany V xs vs).map Prod.fst = V.map Prod.fst :=
  foldl_set_keys (xs.zip vs) V

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

/-! ### Regression examples (checked at build time) -/

-- Constant propagation feeds folding: `let a := 1  let b := add(a, 1)` chains.
example : (propStmts [] [.letDecl ["a"] (some (.lit (.number 1))),
    .letDecl ["b"] (some (.builtin .add [.var "a", .lit (.number 1)])),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "b"])]).1
  = [.letDecl ["a"] (some (.lit (.number 1))),
     .letDecl ["b"] (some (.lit (.number 2))),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 2)])] := rfl
-- Copy propagation: `let y := x` uses become `x`.
example : (propStmts [] [.letDecl ["y"] (some (.var "x")),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "y"])]).1
  = [.letDecl ["y"] (some (.var "x")),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])] := rfl
-- Assignment refresh: reassigned literals are tracked (`multi_reassign`).
example : (propStmts [] [.letDecl ["a"] (some (.lit (.number 1))),
    .assign ["a"] (.lit (.number 2)),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "a"])]).1
  = [.letDecl ["a"] (some (.lit (.number 1))),
     .assign ["a"] (.lit (.number 2)),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 2)])] := rfl
-- Refresh kills stale copies: `y ↦ x` must die when `x` is refreshed.
example : (propStmts [] [.letDecl ["x"] (some (.lit (.number 1))),
    .letDecl ["y"] (some (.var "x")),
    .assign ["x"] (.lit (.number 2)),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "y"])]).1
  = [.letDecl ["x"] (some (.lit (.number 1))),
     .letDecl ["y"] (some (.lit (.number 1))),
     .assign ["x"] (.lit (.number 2)),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- Uninitialized `let` shadows: `let x := 1  let x  use x` must read 0.
example : (propStmts [] [.letDecl ["x"] (some (.lit (.number 1))),
    .letDecl ["x"] none,
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])]).1
  = [.letDecl ["x"] (some (.lit (.number 1))),
     .letDecl ["x"] none,
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 0)])] := rfl
-- A variable assigned inside a loop body is NOT propagated into the loop.
example : (propStmts [] [.letDecl ["i"] (some (.lit (.number 0))),
    .forLoop [] (.builtin .lt [.var "i", .lit (.number 10)])
      [.assign ["i"] (.builtin .add [.var "i", .lit (.number 1)])]
      [.exprStmt (.builtin .sstore [.var "i", .var "i"])]]).1
  = [.letDecl ["i"] (some (.lit (.number 0))),
     .forLoop [] (.builtin .lt [.var "i", .lit (.number 10)])
       [.assign ["i"] (.builtin .add [.var "i", .lit (.number 1)])]
       [.exprStmt (.builtin .sstore [.var "i", .var "i"])]] := rfl
-- funDef bodies restart at σ = [] (no caller-variable capture).
example : (propStmts [] [.letDecl ["x"] (some (.lit (.number 5))),
    .funDef "f" [] ["r"] [.assign ["r"] (.var "x")]]).1
  = [.letDecl ["x"] (some (.lit (.number 5))),
     .funDef "f" [] ["r"] [.assign ["r"] (.var "x")]] := rfl

end YulEvmCompiler.Optimizer
