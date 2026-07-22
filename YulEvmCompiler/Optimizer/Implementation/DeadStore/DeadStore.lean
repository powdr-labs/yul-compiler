import YulEvmCompiler.Optimizer.Implementation.DeadStore.KeyDiff
import YulEvmCompiler.Optimizer.Spec.Pass
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadStore.DeadStore

**Dead-store elimination** for the three EVM memories — persistent storage,
transient storage, and memory — built on the symbolic key-difference analysis in
`KeyDiff`.

## What it removes

A store `s` to location `L` is **dead** when, along every continuation of its
straight-line region, `L` is *overwritten before it is read*: a later store
*covers* `L` with no intervening read of `L`, no control-flow join, no call, and
no halt. Dead stores are dropped; everything else is preserved.

Unlike store-to-load *forwarding* (`StorageForward`, which rewrites later
*reads*), this pass rewrites earlier *writes*. The two are duals.

## The decision procedure (`deadAt`)

Because "dead" is a forward property ("overwritten before read"), we decide each
store by a forward scan of the rest of its block. For a store to key `tk`
(width `wT`) in region `R`, `deadAt` walks the suffix:

* a later **store** to `sk` that *covers* `tk` ⇒ **dead** (stop, `true`);
  a store that is provably **disjoint** ⇒ keep scanning; anything else ⇒ live;
* a **load/observer** at `lk` provably **disjoint** from `tk` ⇒ keep scanning;
  otherwise it may read `tk` ⇒ **live**;
* a **benign** pure binding that does not rebind `tk`'s base variable ⇒ keep
  scanning (a rebind of the base loses the alias relationship ⇒ live);
* anything else (call, control flow, halt, `msize`, unknown) ⇒ **barrier** ⇒ live.

Covering / disjointness come straight from `KeyDiff`: `mustAliasWord` /
`mustNotAliasWord` for the word-addressed regions, `mustCoverMem` /
`mustNotAliasMem` (the `0x20`-window test) for byte-addressed memory.

## Soundness contract

Each per-region traversal is a `Pass` (`Sound`: `EquivBlock b (run b)`), and the
whole thing is their composition. The `Sound` proofs are the deep obligation;
their statements are given here and their bodies are `sorry` (intermediate
steps), with the invariant sketched in the `Soundness` section.
-/

namespace YulEvmCompiler.Optimizer.DeadStore

open YulSemantics
open YulSemantics.EVM

/-! ### Region descriptor -/

/-- The three independently-tracked EVM memories. Storage and transient storage
are **word-addressed** (alias iff key words equal); memory is **byte-ranged**
(alias iff 32-byte windows overlap). -/
inductive Region
  | storage | transient | memory
  deriving DecidableEq, Repr

/-- The byte width a store op writes in region `R` (word regions use `0`, unused).
`none` when `op` is not a store for `R`. -/
def regionStoreWidth : Region → Op → Option Int
  | .storage,   .sstore  => some 0
  | .transient, .tstore  => some 0
  | .memory,    .mstore  => some 32
  | .memory,    .mstore8 => some 1
  | _,          _        => none

/-- The width a load op observes in region `R`. `none` when `op` is not a load
for `R`. -/
def regionLoadWidth : Region → Op → Option Int
  | .storage,   .sload => some 0
  | .transient, .tload => some 0
  | .memory,    .mload => some 32
  | _,          _      => none

/-! ### The pure / total / observer-free expression fragment

An expression is *clean* when it is built from literals, variables, and
pure-total arithmetic only: it never halts, never reads or writes any region,
and always evaluates. Removing the evaluation of a clean expression is
unobservable — the property that lets us delete a store whose key and value are
clean. Mirrors `DeadPure.pureTotalArity`. -/

/-- Arity at which an op is pure and total on words (`none` outside the pure
fragment). -/
def pureArith : Op → Option Nat
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod
  | .signextend | .lt | .gt | .slt | .sgt | .eq
  | .and | .or | .xor | .byte | .shl | .shr | .sar => some 2
  | .clz | .iszero | .not => some 1
  | .addmod | .mulmod => some 3
  | _ => none

mutual
/-- `true` when `e` is a pure, total, observer-free expression. -/
def cleanExpr : Expr Op → Bool
  | .lit _ => true
  | .var _ => true
  | .builtin op args => (pureArith op == some args.length) && cleanArgs args
  | .call _ _ => false
/-- `cleanExpr` lifted to argument lists. -/
def cleanArgs : List (Expr Op) → Bool
  | [] => true
  | e :: rest => cleanExpr e && cleanArgs rest
end

/-- A key is *analyzable* when its base is the constant base or a single
variable — the two stable base shapes the traversal can track. -/
def analyzableKey (k : Expr Op) : Bool :=
  match keyBase k with
  | .lit (.number 0) => true      -- the canonical constant base
  | .var _           => true
  | _                => false

mutual
/-- `true` when `e` contains no variables. A deletable store's *value* must be
variable-free: removing the store removes the evaluation of its value, so — to
keep unbound-variable *stuckness* unchanged (`EquivBlock` quantifies over every
environment) — the value must be guaranteed to evaluate regardless of the
environment. A clean variable-free expression (literals + pure-total arithmetic)
always evaluates. (The store's *key* may use a variable base: the covering store
references the same base, so wherever the transformed program evaluates, the
base is bound and the removed key would have evaluated too.) -/
def varFreeExpr : Expr Op → Bool
  | .lit _ => true
  | .var _ => false
  | .builtin _ args => varFreeArgs args
  | .call _ args => varFreeArgs args
/-- `varFreeExpr` lifted to argument lists. -/
def varFreeArgs : List (Expr Op) → Bool
  | [] => true
  | e :: rest => varFreeExpr e && varFreeArgs rest
end

/-! ### Statement classification -/

/-- What a straight-line statement does to region `R`, from the traversal's point
of view. `store`/`load` carry the analyzable key and its width; `binds` lists the
variables the statement (re)binds (used to detect a base being clobbered);
`barrier` conservatively subsumes everything else. -/
inductive Ev
  | store   (key : Expr Op) (width : Int)
  | load    (key : Expr Op) (width : Int) (binds : List Ident)
  | benign  (binds : List Ident)
  | barrier

/-- Recognize a single-key load `loadOp k` for region `R`. -/
def loadKeyOf (R : Region) : Expr Op → Option (Expr Op × Int)
  | .builtin op [k] => (regionLoadWidth R op).map (fun w => (k, w))
  | _ => none

/-- A number-literal expression. Deletable stores are restricted to literal keys
and values: after the pipeline's constant folding and propagation, a slot and the
value written to it are typically literals, and literals evaluate trivially and
state-independently — which is what makes the removal's simulation tractable to
verify. The nonzero-constant key-difference analysis still applies fully to
literal slots (`sstore(0,_); sstore(1,_); sstore(0,_)` drops the first). -/
def litKey : Expr Op → Bool
  | .lit (.number _) => true
  | _ => false

/-- Classify a statement for region `R`. -/
def classify (R : Region) : Stmt Op → Ev
  | .exprStmt (.builtin op [k, v]) =>
      match regionStoreWidth R op with
      | some w =>
          -- deletable store: a literal key and a literal value (see `litKey`).
          if litKey k && litKey v then .store k w else .barrier
      | none => .barrier
  | .letDecl xs (some rhs) =>
      match loadKeyOf R rhs with
      | some (lk, w) => if analyzableKey lk && cleanExpr lk then .load lk w xs else .barrier
      | none => if cleanExpr rhs then .benign xs else .barrier
  | .assign xs rhs =>
      match loadKeyOf R rhs with
      | some (lk, w) => if analyzableKey lk && cleanExpr lk then .load lk w xs else .barrier
      | none => if cleanExpr rhs then .benign xs else .barrier
  | .letDecl xs none => .benign xs
  | _ => .barrier

/-! ### Covering / disjointness, region-dispatched -/

/-- A later store at `sk` (width `wS`) *covers* the earlier target `tk`
(width `wT`). -/
def covers : Region → Expr Op → Int → Expr Op → Int → Bool
  | .memory, sk, wS, tk, wT => mustCoverMem sk wS tk wT
  | _,       sk, _,  tk, _  => mustAliasWord sk tk

/-- An access at `k₁` (width `w₁`) is provably disjoint from the target `k₂`
(width `w₂`). -/
def disjoint : Region → Expr Op → Int → Expr Op → Int → Bool
  | .memory, k₁, w₁, k₂, w₂ => mustNotAliasMem k₁ w₁ k₂ w₂
  | _,       k₁, _,  k₂, _  => mustNotAliasWord k₁ k₂

/-- Does the statement rebind the target key's base variable? (A constant base is
never affected.) -/
def rebindsBase (tk : Expr Op) (binds : List Ident) : Bool :=
  binds.any (fun x => beqExpr (keyBase tk) (.var x))

/-! ### The forward deadness scan -/

/-- Whether stores in region `R` **halt exceptionally in a static frame**
(`sstore`/`tstore` do; `mstore`/`mstore8` do not). In such a region a dead store
would halt *before* any intervening statement runs, whereas the reduced program
runs those statements (changing the variable environment) before halting — so
removal is only sound across statements that **also** halt immediately in a
static frame, i.e. other stores. Intervening `benign`/`load` statements
(which change the environment without halting) must therefore be treated as
barriers for these regions. -/
def haltsInStatic : Region → Bool
  | .memory => false
  | _       => true

/-- `deadAt R tk wT rest` is `true` when a store to key `tk` (width `wT`) in
region `R` is dead given the continuation `rest`: `tk` is overwritten by a later
store before any *other* kind of statement.

The scan skips only provably-**disjoint stores** (which neither read `tk` nor
change the variable environment, and — crucially — halt exactly when the dead
store would in a static frame, so the halting behavior stays symmetric) until a
**covering store**. Any non-store statement (`load`/`benign`/`barrier`) stops the
scan. This is more conservative than skipping benign bindings, but it keeps the
soundness proof to two local rewrites (commute past a disjoint store, cancel
against a covering store) and still exercises the full symbolic
key-difference analysis: `disjoint` uses the nonzero-constant /
`0x20`-window tests, `covers` uses the zero-difference / containment tests. -/
def deadAt (R : Region) (tk : Expr Op) (wT : Int) : List (Stmt Op) → Bool
  | [] => false
  | s :: rest =>
      match classify R s with
      | .store sk wS =>
          if covers R sk wS tk wT then true
          else if disjoint R sk wS tk wT then deadAt R tk wT rest
          else false
      | _ => false

/-! ### The traversal -/

mutual
/-- Optimize a single statement's nested blocks for region `R` (each nested block
is a fresh straight-line region — pending never crosses a control-flow or loop
boundary). -/
def dseStmt (R : Region) : Stmt Op → Stmt Op
  | .block body => .block (dseStmts R body)
  | .cond c body => .cond c (dseStmts R body)
  | .switch c cases dflt =>
      .switch c (dseCases R cases) (dseDflt R dflt)
  -- `init` is left untouched: it is both executed and hoisted across the whole
  -- loop, so `forLoop_congr` fixes it. Only `post`/`body` are optimized.
  | .forLoop init c post body =>
      .forLoop init c (dseStmts R post) (dseStmts R body)
  -- function bodies are left untouched (shallow): rewriting a `funDef` body
  -- changes the hoisted `FScope`, which `EquivBlock.of_stmts` forbids.
  | .funDef n ps rs body => .funDef n ps rs body
  | s => s

/-- Optimize a straight-line statement list for region `R`, dropping dead stores. -/
def dseStmts (R : Region) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest =>
      let s' := dseStmt R s
      match classify R s with
      | .store sk wS => if deadAt R sk wS rest then dseStmts R rest else s' :: dseStmts R rest
      | _ => s' :: dseStmts R rest

/-- Optimize each `switch` case body. -/
def dseCases (R : Region) : List (Literal × List (Stmt Op)) → List (Literal × List (Stmt Op))
  | [] => []
  | (l, b) :: rest => (l, dseStmts R b) :: dseCases R rest

/-- Optimize a `switch` default body. -/
def dseDflt (R : Region) : Option (List (Stmt Op)) → Option (List (Stmt Op))
  | none => none
  | some b => some (dseStmts R b)
end

/-- Whole-block dead-store elimination: storage, then transient, then memory.
Each region pass is independently sound, so the order is immaterial. -/
def deadStoreBlock (b : Block Op) : Block Op :=
  dseStmts .memory (dseStmts .transient (dseStmts .storage b))

/-! ### Soundness

Each per-region traversal preserves semantics. The invariant behind the forward
scan is:

> *If `deadAt R tk wT rest = true`, then for every configuration, executing
> `store tk _ :: rest` and executing `rest` reach the same final `(V, st, o)`.*

Because `deadAt` guarantees `tk` is overwritten by a covering store `cov ∈ rest`
before any read of `tk`, any barrier, or any control-flow escape, the two runs
differ only in `st`'s region-`R` value at the byte range of `tk`, over the span
up to `cov`; that range is never read there, and `cov` writes the same final
value in both runs, after which the states coincide. (Stores are `reads = false`
in the dialect's `effects`, so an intervening disjoint store never observes
`tk`; clean keys/values never observe or halt.) Lifting the local fact through
the `YulSemantics.Equiv` statement congruences gives `EquivBlock`.

The proofs are the deep obligation and are left as `sorry` here. -/

section Sound
variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-- **Local deadness ⇒ prefix equivalence** — the semantic heart of the pass.
When `s` classifies as a dead store to `tk` (width `wT`) that `deadAt` finds
overwritten before any read along `rest`, prepending `s` to `rest` is
`EquivStmts`-equivalent to `rest` alone.

Taking `s` and its `classify` fact directly (rather than the exploded
`exprStmt (builtin …)` form) lets the structural pass `dseStmts_sound` invoke it
without re-deriving the shape. The proof is the deep forward-simulation
(state-agreement up to the covering store, with static-frame halt symmetry and,
for memory, byte-range commutation); it is the one remaining `sorry`. -/
theorem deadAt_sound (R : Region) (s : Stmt Op) (tk : Expr Op) (wT : Int)
    (rest : List (Stmt Op))
    (hclass : classify R s = .store tk wT)
    (hdead : deadAt R tk wT rest = true) :
    EquivStmts D (s :: rest) rest := by
  sorry

/-! #### Structural reduction of `dseStmts_sound` to `deadAt_sound`

Everything below is proved outright; the pass's soundness rests only on
`deadAt_sound` above. -/

/-- A dead store never classifies as a `funDef`, so it is invisible to `hoist`. -/
theorem classify_store_shape {R : Region} {s : Stmt Op} {tk : Expr Op} {wT : Int}
    (h : classify R s = .store tk wT) :
    ∃ op v, s = .exprStmt (.builtin op [tk, v]) := by
  cases s with
  | exprStmt e =>
      cases e with
      | builtin op args =>
          match args with
          | [] => simp [classify] at h
          | [_] => simp [classify] at h
          | [k, v] =>
              refine ⟨op, v, ?_⟩
              simp only [classify] at h
              split at h
              · split at h
                · rename_i w _ _
                  rw [Ev.store.injEq] at h; rw [h.1]
                · simp at h
              · simp at h
          | _ :: _ :: _ :: _ => simp [classify] at h
      | lit _ => simp [classify] at h
      | var _ => simp [classify] at h
      | call _ _ => simp [classify] at h
  | letDecl xs val =>
      cases val with
      | none => simp [classify] at h
      | some rhs =>
          simp only [classify] at h
          split at h
          · split at h <;> simp at h
          · split at h <;> simp at h
  | assign xs rhs =>
      simp only [classify] at h
      split at h
      · split at h <;> simp at h
      · split at h <;> simp at h
  | block _ => simp [classify] at h
  | funDef _ _ _ _ => simp [classify] at h
  | cond _ _ => simp [classify] at h
  | switch _ _ _ => simp [classify] at h
  | forLoop _ _ _ _ => simp [classify] at h
  | «break» => simp [classify] at h
  | «continue» => simp [classify] at h
  | leave => simp [classify] at h

/-- Replacing a statement's head by its DSE-transformed form leaves the block's
hoisted `funDef` scope unchanged (DSE preserves `funDef`-ness). -/
theorem hoist_cons_dseStmt (R : Region) (s : Stmt Op) (l : Block Op) :
    hoist D (dseStmt R s :: l) = hoist D (s :: l) := by
  cases s <;> simp [dseStmt, hoist]

/-- Rewriting the tail preserves the block's hoisted scope. -/
theorem hoist_cons_tail (s : Stmt Op) {l₁ l₂ : Block Op} (h : hoist D l₁ = hoist D l₂) :
    hoist D (s :: l₁) = hoist D (s :: l₂) := by
  cases s <;> simpa [hoist] using h

/-- Dead-store elimination preserves the hoisted function scope of every block:
it never removes or rewrites a `funDef` statement. -/
theorem dseStmts_hoist (R : Region) (b : Block Op) :
    hoist D (dseStmts R b) = hoist D b := by
  induction b with
  | nil => rfl
  | cons s rest ih =>
      simp only [dseStmts]
      split
      · -- classify = store
        rename_i sk wS hclass
        obtain ⟨op, v, rfl⟩ := classify_store_shape hclass
        split
        · -- dead ⇒ dropped; the head is an `exprStmt`, invisible to `hoist`
          simpa [hoist, dseStmt] using ih
        · -- kept; the head is the same `exprStmt`
          simpa [hoist, dseStmt] using ih
      · -- other ⇒ kept
        rw [hoist_cons_dseStmt]
        exact hoist_cons_tail s ih

-- The congruence: each traversal produces a semantically-equivalent program.
-- Mutual over the four traversal functions.
mutual
theorem dseStmt_equiv (R : Region) : ∀ s : Stmt Op, EquivStmt D s (dseStmt R s)
  | .block body => by
      rw [dseStmt]
      exact EquivBlock.of_stmts (dseStmts_equiv R body) (dseStmts_hoist R body).symm
  | .cond c body => by
      rw [dseStmt]
      exact EquivStmt.cond_congr (@EquivExpr.refl D _ c)
        (EquivBlock.of_stmts (dseStmts_equiv R body) (dseStmts_hoist R body).symm)
  | .switch c cases dflt => by
      rw [dseStmt]
      exact EquivStmt.switch_congr (@EquivExpr.refl D _ c)
        (dseCases_forall2 R cases) (dseDflt_equiv R dflt)
  | .forLoop init c post body => by
      rw [dseStmt]
      exact EquivStmt.forLoop_congr init (@EquivExpr.refl D _ c)
        (EquivBlock.of_stmts (dseStmts_equiv R post) (dseStmts_hoist R post).symm)
        (EquivBlock.of_stmts (dseStmts_equiv R body) (dseStmts_hoist R body).symm)
  | .funDef n ps rs body => EquivStmt.refl _
  | .letDecl _ _ => EquivStmt.refl _
  | .assign _ _ => EquivStmt.refl _
  | .exprStmt _ => EquivStmt.refl _
  | .break => EquivStmt.refl _
  | .continue => EquivStmt.refl _
  | .leave => EquivStmt.refl _
theorem dseStmts_equiv (R : Region) : ∀ ss : List (Stmt Op), EquivStmts D ss (dseStmts R ss)
  | [] => by rw [dseStmts]; exact EquivStmts.refl []
  | s :: rest => by
      simp only [dseStmts]
      split
      · rename_i sk wS hclass
        split
        · rename_i hdead
          exact (deadAt_sound R s sk wS rest hclass hdead).trans (dseStmts_equiv R rest)
        · exact EquivStmts.cons_congr (dseStmt_equiv R s) (dseStmts_equiv R rest)
      · exact EquivStmts.cons_congr (dseStmt_equiv R s) (dseStmts_equiv R rest)
theorem dseCases_forall2 (R : Region) : ∀ cases : List (Literal × List (Stmt Op)),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cases (dseCases R cases)
  | [] => by rw [dseCases]; exact List.Forall₂.nil
  | (l, b) :: rest => by
      rw [dseCases]
      exact List.Forall₂.cons ⟨rfl, EquivBlock.of_stmts (dseStmts_equiv R b) (dseStmts_hoist R b).symm⟩
        (dseCases_forall2 R rest)
theorem dseDflt_equiv (R : Region) : ∀ dflt : Option (List (Stmt Op)),
    EquivBlock D (dflt.getD []) ((dseDflt R dflt).getD [])
  | none => by rw [dseDflt]; exact EquivBlock.refl []
  | some b => by
      rw [dseDflt]
      exact EquivBlock.of_stmts (dseStmts_equiv R b) (dseStmts_hoist R b).symm
end

/-- Each per-region traversal is semantics-preserving. -/
theorem dseStmts_sound (R : Region) : Sound D (dseStmts R) := fun b =>
  EquivBlock.of_stmts (dseStmts_equiv R b) (dseStmts_hoist R b).symm

/-- A per-region traversal, packaged as a verified pass. -/
def deadStorePass (R : Region) : Pass D where
  run := dseStmts R
  sound := dseStmts_sound R

/-- Whole-block dead-store elimination as a verified pass: the composition of the
three region passes. -/
def deadStore : Pass D :=
  (deadStorePass .memory).comp ((deadStorePass .transient).comp (deadStorePass .storage))

@[simp] theorem deadStore_run (b : Block Op) : (deadStore (calls := calls) (creates := creates)).run b = deadStoreBlock b := rfl

/-- End-to-end: `deadStore` preserves whole-program behavior (`Run`). -/
theorem deadStore_preservesRun (b : Block Op) {st0 V' st' o} :
    Run D b st0 V' st' o ↔
      Run D ((deadStore (calls := calls) (creates := creates)).run b) st0 V' st' o :=
  (deadStore (calls := calls) (creates := creates)).preservesRun b

end Sound

end YulEvmCompiler.Optimizer.DeadStore
