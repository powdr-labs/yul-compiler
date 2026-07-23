import YulEvmCompiler.Optimizer.Implementation.DeadStore.KeyDiff
import YulEvmCompiler.Optimizer.Spec.Pass
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadStore.DeadStore

**Dead-store elimination** built on the symbolic key-difference analysis in
`KeyDiff`. The design covers all three EVM memories (persistent storage,
transient storage, and byte-addressed memory); the pass currently **enables and
fully verifies the storage region** (`regionStoreWidth`), with transient and
memory staged behind the same machinery (see the `Soundness` note).

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
whole thing is their composition. The `Sound` proofs are **complete** (no proof holes)
for the currently-enabled region (storage); see the `Soundness` section.
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
-- NOTE: the memory region is currently disabled in the pass (it produces no
-- store events, so memory dead-store elimination is a no-op) pending the
-- byte-range simulation proof for `storeWord`/`touchMemory`. The symbolic memory
-- analysis (`mustCoverMem`/`mustNotAliasMem`, the `0x20`-window tests) is proved
-- in `KeyDiff` and ready to enable. Only the word-addressed regions
-- (storage/transient) currently perform elimination.
def regionStoreWidth : Region → Op → Option Int
  | .storage,   .sstore  => some 0
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

This is now **fully proved** (`deadAt_sound` and `dseStmts_sound`
depend only on the three standard classical axioms). The proof is developed for
the word-addressed regions with literal keys/values via `sstore_step_iff` (the
store's exact effect), the effect algebra (`sstoreEff_absorb`/`sstoreEff_comm`),
the reusable `sstore_prepend`, and the local rewrites `cancel_tail`
(overwrite) / `commute_tail` (disjoint), assembled by induction on the scan
(`deadAt_sound_storage`). The transient and memory regions are currently
disabled in `regionStoreWidth` (so their `deadAt_sound` cases are vacuous);
enabling transient is a near-copy of the storage development, and memory needs
the `storeWord`/`touchMemory` byte-range analogues. -/

section Sound
variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

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
def sstoreEff (st : EvmState) (kw vw : U256) : EvmState :=
  { st with storage := upd st.storage kw vw, env := { st.env with storageOf := updAccount st.env.storageOf st.env.address kw vw } }

theorem stepOp_sstore (kw vw : U256) (st : EvmState) :
    stepOp .sstore [kw, vw] st
      = some (if st.env.static then .halt { st with halted := some (.staticViolation, []) }
              else .ok [] (sstoreEff st kw vw)) := rfl

theorem builtin_sstore_iff (kw vw : U256) (st : EvmState) (r) :
    (D).Builtin .sstore [kw, vw] st r ↔ stepOp .sstore [kw, vw] st = some r := Iff.rfl

theorem lit_args_eval (kk vv : Nat) (funs : FunEnv D) (V : VEnv D) (st : EvmState) :
    Step D funs V st (.args [.lit (.number kk), .lit (.number vv)])
      (.eres (.vals [litValue (.number kk), litValue (.number vv)] st)) :=
  Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit

theorem lit_args_inv (kk vv : Nat) {funs : FunEnv D} {V : VEnv D} {st : EvmState} {r}
    (h : Step D funs V st (.args [.lit (.number kk), .lit (.number vv)]) (.eres r)) :
    r = .vals [litValue (.number kk), litValue (.number vv)] st := by
  cases h with
  | argsCons hrest hhead => cases hhead with
    | lit => cases hrest with
      | argsCons hrest2 hhead2 => cases hhead2 with
        | lit => cases hrest2 with | argsNil => rfl
  | argsRestHalt hrest => cases hrest with
    | argsRestHalt h2 => cases h2
    | argsHeadHalt _ h2 => cases h2
  | argsHeadHalt hrest hhead => cases hhead

theorem sstore_step_iff (kk vv : Nat) {funs : FunEnv D} {V : VEnv D} {st : EvmState} {V' st' o} :
    Step D funs V st
      (.stmt (.exprStmt (.builtin .sstore [.lit (.number kk), .lit (.number vv)]))) (.sres V' st' o)
    ↔ (V' = V ∧
        ((st.env.static = false ∧ st' = sstoreEff st (litValue (.number kk)) (litValue (.number vv))
            ∧ o = .normal)
         ∨ (st.env.static = true ∧ st' = { st with halted := some (.staticViolation, []) }
            ∧ o = .halt))) := by
  constructor
  · intro h
    cases h with
    | exprStmt he => cases he with
      | builtinOk hargs hb =>
          have hi := lit_args_inv kk vv hargs
          injection hi with hvals hst; rw [hvals, hst] at hb
          rw [builtin_sstore_iff, stepOp_sstore] at hb
          cases hs : st.env.static with
          | false => rw [if_neg (by rw [hs]; decide)] at hb
                     simp only [Option.some.injEq, BuiltinResult.ok.injEq] at hb
                     exact ⟨rfl, Or.inl ⟨rfl, hb.2.symm, rfl⟩⟩
          | true => rw [if_pos (by rw [hs])] at hb
                    simp only [Option.some.injEq] at hb; exact absurd hb (by simp)
    | exprStmtHalt he => cases he with
      | builtinHalt hargs hb =>
          have hi := lit_args_inv kk vv hargs
          injection hi with hvals hst; rw [hvals, hst] at hb
          rw [builtin_sstore_iff, stepOp_sstore] at hb
          cases hs : st.env.static with
          | false => rw [if_neg (by rw [hs]; decide)] at hb
                     simp only [Option.some.injEq] at hb; exact absurd hb (by simp)
          | true => rw [if_pos (by rw [hs])] at hb
                    simp only [Option.some.injEq, BuiltinResult.halt.injEq] at hb
                    exact ⟨rfl, Or.inr ⟨rfl, hb.symm, rfl⟩⟩
      | builtinArgsHalt hargs => exact absurd (lit_args_inv kk vv hargs) (by simp)
  · rintro ⟨rfl, (⟨hs, rfl, rfl⟩ | ⟨hs, rfl, rfl⟩)⟩
    · refine Step.exprStmt (Step.builtinOk (lit_args_eval kk vv _ _ _) ?_)
      rw [builtin_sstore_iff, stepOp_sstore, if_neg (by rw [hs]; decide)]
    · refine Step.exprStmtHalt (Step.builtinHalt (lit_args_eval kk vv _ _ _) ?_)
      rw [builtin_sstore_iff, stepOp_sstore, if_pos (by rw [hs])]

-- ### sequence inversion helpers
theorem stmts_single_iff {funs : FunEnv D} {V : VEnv D} {st s V' st' o} :
    Step D funs V st (.stmts [s]) (.sres V' st' o) ↔ Step D funs V st (.stmt s) (.sres V' st' o) := by
  constructor
  · intro h; cases h with
    | seqCons hs hrest => cases hrest with | seqNil => exact hs
    | seqStop hs _ => exact hs
  · intro h
    by_cases ho : o = .normal
    · subst ho; exact Step.seqCons h Step.seqNil
    · exact Step.seqStop h ho

theorem stmts_cons_fwd {funs : FunEnv D} {V : VEnv D} {st s rest V' st' o}
    (h : Step D funs V st (.stmts (s :: rest)) (.sres V' st' o)) :
    (∃ V1 st1, Step D funs V st (.stmt s) (.sres V1 st1 .normal) ∧
        Step D funs V1 st1 (.stmts rest) (.sres V' st' o))
    ∨ (Step D funs V st (.stmt s) (.sres V' st' o) ∧ o ≠ .normal) := by
  cases h with
  | seqCons hs hrest => exact Or.inl ⟨_, _, hs, hrest⟩
  | seqStop hs hne => exact Or.inr ⟨hs, hne⟩

-- ### effect algebra
theorem upd_upd_same (f : U256 → U256) (k v v' : U256) :
    upd (upd f k v) k v' = upd f k v' := by
  funext x; simp only [upd]; split <;> rfl

theorem upd_comm (f : U256 → U256) (k1 v1 k2 v2 : U256) (h : k1 ≠ k2) :
    upd (upd f k1 v1) k2 v2 = upd (upd f k2 v2) k1 v1 := by
  funext x; simp only [upd]
  by_cases hx1 : x = k1 <;> by_cases hx2 : x = k2 <;> simp_all

theorem updAccount_upd_same (f : U256 → U256 → U256) (a k v v' : U256) :
    updAccount (updAccount f a k v) a k v' = updAccount f a k v' := by
  funext x y; simp only [updAccount]
  by_cases h1 : accountKey x = accountKey a <;> by_cases h2 : y = k <;> simp [h1, h2]

theorem updAccount_comm (f : U256 → U256 → U256) (a k1 v1 k2 v2 : U256) (h : k1 ≠ k2) :
    updAccount (updAccount f a k1 v1) a k2 v2 = updAccount (updAccount f a k2 v2) a k1 v1 := by
  funext x y; simp only [updAccount]
  by_cases h1 : accountKey x = accountKey a <;>
    by_cases hy1 : y = k1 <;> by_cases hy2 : y = k2 <;> simp_all

-- ### sstoreEff algebra
@[simp] theorem sstoreEff_static (st kw vw) : (sstoreEff st kw vw).env.static = st.env.static := rfl
@[simp] theorem sstoreEff_addr (st kw vw) : (sstoreEff st kw vw).env.address = st.env.address := rfl
@[simp] theorem sstoreEff_halted (st kw vw) : (sstoreEff st kw vw).halted = st.halted := rfl

theorem sstoreEff_absorb (st kw vw vw') :
    sstoreEff (sstoreEff st kw vw) kw vw' = sstoreEff st kw vw' := by
  simp only [sstoreEff, upd_upd_same, updAccount_upd_same]

theorem sstoreEff_comm (st k1 v1 k2 v2) (h : k1 ≠ k2) :
    sstoreEff (sstoreEff st k1 v1) k2 v2 = sstoreEff (sstoreEff st k2 v2) k1 v1 := by
  simp only [sstoreEff]
  rw [upd_comm _ _ _ _ _ (Ne.symm h), updAccount_comm _ _ _ _ _ _ (Ne.symm h)]

def sstoreStmt (kk vv : Nat) : Stmt Op :=
  .exprStmt (.builtin .sstore [.lit (.number kk), .lit (.number vv)])

theorem sstore_prepend (kk vv : Nat) (rest : List (Stmt Op)) {funs : FunEnv D} {V : VEnv D}
    {st : EvmState} {V' st' o} :
    ExecStmts D funs V st (sstoreStmt kk vv :: rest) V' st' o
    ↔ (st.env.static = false ∧ ExecStmts D funs V
          (sstoreEff st (litValue (.number kk)) (litValue (.number vv))) rest V' st' o)
      ∨ (st.env.static = true ∧ V' = V ∧ st' = { st with halted := some (.staticViolation, []) }
          ∧ o = .halt) := by
  constructor
  · intro h
    rcases stmts_cons_fwd h with ⟨V1, st1, hs, hrest⟩ | ⟨hs, hne⟩
    · simp only [sstoreStmt] at hs; rw [sstore_step_iff] at hs
      obtain ⟨rfl, (⟨hst, rfl, _⟩ | ⟨_, _, hcontra⟩)⟩ := hs
      · exact Or.inl ⟨hst, hrest⟩
      · exact absurd hcontra (by simp)
    · simp only [sstoreStmt] at hs; rw [sstore_step_iff] at hs
      obtain ⟨rfl, (⟨_, _, hcontra⟩ | ⟨hst, rfl, rfl⟩)⟩ := hs
      · exact absurd hcontra hne
      · exact Or.inr ⟨hst, rfl, rfl, rfl⟩
  · rintro (⟨hst, hrest⟩ | ⟨hst, rfl, rfl, rfl⟩)
    · exact Step.seqCons (by simp only [sstoreStmt]; exact (sstore_step_iff kk vv).mpr ⟨rfl, Or.inl ⟨hst, rfl, rfl⟩⟩) hrest
    · exact Step.seqStop (by simp only [sstoreStmt]; exact (sstore_step_iff kk vv).mpr ⟨rfl, Or.inr ⟨hst, rfl, rfl⟩⟩) (by simp)

theorem cancel_tail (kk vv vv2 : Nat) (rest' : List (Stmt Op)) :
    EquivStmts D (sstoreStmt kk vv :: sstoreStmt kk vv2 :: rest') (sstoreStmt kk vv2 :: rest') := by
  intro funs V st V' st' o
  constructor
  · intro h
    rw [sstore_prepend] at h
    rcases h with ⟨hst, h⟩ | ⟨hst, rfl, rfl, rfl⟩
    · rw [sstore_prepend] at h
      rw [sstore_prepend]
      rcases h with ⟨_, h2⟩ | ⟨hst2, _⟩
      · exact Or.inl ⟨hst, by rw [sstoreEff_absorb] at h2; exact h2⟩
      · rw [sstoreEff_static, hst] at hst2; exact absurd hst2 (by simp)
    · rw [sstore_prepend]; exact Or.inr ⟨hst, rfl, rfl, rfl⟩
  · intro h
    rw [sstore_prepend] at h
    rw [sstore_prepend]
    rcases h with ⟨hst, h2⟩ | ⟨hst, rfl, rfl, rfl⟩
    · refine Or.inl ⟨hst, ?_⟩
      rw [sstore_prepend]; exact Or.inl ⟨by rw [sstoreEff_static]; exact hst,
        by rw [sstoreEff_absorb]; exact h2⟩
    · exact Or.inr ⟨hst, rfl, rfl, rfl⟩

theorem commute_tail (kk vv kk2 vv2 : Nat) (rest' : List (Stmt Op))
    (hne : litValue (.number kk) ≠ litValue (.number kk2)) :
    EquivStmts D (sstoreStmt kk vv :: sstoreStmt kk2 vv2 :: rest')
      (sstoreStmt kk2 vv2 :: sstoreStmt kk vv :: rest') := by
  intro funs V st V' st' o
  constructor
  · intro h
    rw [sstore_prepend] at h; rw [sstore_prepend]
    rcases h with ⟨hst, h⟩ | ⟨hst, rfl, rfl, rfl⟩
    · rw [sstore_prepend] at h
      rcases h with ⟨_, h2⟩ | ⟨hst2, _⟩
      · refine Or.inl ⟨hst, ?_⟩
        rw [sstore_prepend]
        exact Or.inl ⟨by rw [sstoreEff_static]; exact hst,
          by rw [sstoreEff_comm st _ _ _ _ hne] at h2; exact h2⟩
      · rw [sstoreEff_static, hst] at hst2; exact absurd hst2 (by simp)
    · exact Or.inr ⟨hst, rfl, rfl, rfl⟩
  · intro h
    rw [sstore_prepend] at h; rw [sstore_prepend]
    rcases h with ⟨hst, h⟩ | ⟨hst, rfl, rfl, rfl⟩
    · rw [sstore_prepend] at h
      rcases h with ⟨_, h2⟩ | ⟨hst2, _⟩
      · refine Or.inl ⟨hst, ?_⟩
        rw [sstore_prepend]
        exact Or.inl ⟨by rw [sstoreEff_static]; exact hst,
          by rw [sstoreEff_comm st _ _ _ _ (Ne.symm hne)] at h2; exact h2⟩
      · rw [sstoreEff_static, hst] at hst2; exact absurd hst2 (by simp)
    · exact Or.inr ⟨hst, rfl, rfl, rfl⟩

-- ### bridges from the alias predicates to key facts
theorem offWord_lit (n : Nat) : offWord (n : Int) = litValue (.number n) := by
  simp only [offWord, litValue, BitVec.ofInt_natCast]

theorem litKey_inv {k : Expr Op} (h : litKey k = true) : ∃ n, k = .lit (.number n) := by
  match k with
  | .lit (.number n) => exact ⟨n, rfl⟩
  | .lit (.bool _) => simp [litKey] at h
  | .lit (.string _) => simp [litKey] at h
  | .var _ => simp [litKey] at h
  | .builtin _ _ => simp [litKey] at h
  | .call _ _ => simp [litKey] at h

theorem covers_storage {kk2 kk : Nat} {wS wT : Int}
    (h : covers .storage (.lit (.number kk2)) wS (.lit (.number kk)) wT = true) : kk2 = kk := by
  simp only [covers, mustAliasWord, keyDelta, keyBase, keyOff, splitKey, beqExpr_refl,
    if_true, beq_iff_eq, Option.some.injEq] at h
  omega

theorem disjoint_storage {kk2 kk : Nat} {wS wT : Int}
    (h : disjoint .storage (.lit (.number kk2)) wS (.lit (.number kk)) wT = true) :
    litValue (.number kk) ≠ litValue (.number kk2) := by
  simp only [disjoint, mustNotAliasWord, keyDelta, keyBase, keyOff, splitKey, beqExpr_refl,
    if_true, decide_eq_true_eq] at h
  have hne := word_ne_of_delta_ne_zero 0 (kk2 : Int) (kk : Int) h.1 h.2
  rw [zero_add, zero_add, offWord_lit, offWord_lit] at hne
  exact fun heq => hne heq.symm

theorem regionStoreWidth_storage {op w} (h : regionStoreWidth .storage op = some w) :
    op = .sstore := by cases op <;> simp_all [regionStoreWidth]

theorem classify_storage_inv {s : Stmt Op} {tk wT} (h : classify .storage s = .store tk wT) :
    ∃ kk vv, s = sstoreStmt kk vv ∧ tk = .lit (.number kk) := by
  obtain ⟨op, v, rfl⟩ := classify_store_shape h
  simp only [classify] at h
  split at h
  · rename_i w hw
    have hop := regionStoreWidth_storage hw
    split at h
    · rename_i hg
      simp only [Bool.and_eq_true] at hg
      obtain ⟨kk, rfl⟩ := litKey_inv hg.1
      obtain ⟨vv, rfl⟩ := litKey_inv hg.2
      exact ⟨kk, vv, by simp only [hop, sstoreStmt], rfl⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem deadAt_sound_storage (kk vv : Nat) (wT : Int) : ∀ rest : List (Stmt Op),
    deadAt .storage (.lit (.number kk)) wT rest = true →
    EquivStmts D (sstoreStmt kk vv :: rest) rest := by
  intro rest
  induction rest with
  | nil => intro hdead; simp [deadAt] at hdead
  | cons s' rest' ih =>
      intro hdead
      simp only [deadAt] at hdead
      split at hdead
      · rename_i sk wS hclass
        obtain ⟨kk2, vv2, rfl, hsk⟩ := classify_storage_inv hclass
        subst hsk
        split at hdead
        · rename_i hcov
          have hkk : kk2 = kk := covers_storage hcov
          subst kk2
          exact cancel_tail kk vv vv2 rest'
        · split at hdead
          · rename_i hdisj
            exact (commute_tail kk vv kk2 vv2 rest' (disjoint_storage hdisj)).trans
              (EquivStmts.cons_congr (EquivStmt.refl _) (ih hdead))
          · simp at hdead
      · simp at hdead

-- top-level, matching DeadStore.deadAt_sound (storage enabled; other regions vacuous
-- because their regionStoreWidth is `none`, so classify never yields `.store`)
theorem deadAt_sound (R : Region) (s : Stmt Op) (tk : Expr Op) (wT : Int)
    (rest : List (Stmt Op)) (hclass : classify R s = .store tk wT)
    (hdead : deadAt R tk wT rest = true) : EquivStmts D (s :: rest) rest := by
  cases R with
  | storage =>
      obtain ⟨kk, vv, rfl, htk⟩ := classify_storage_inv hclass
      subst htk
      exact deadAt_sound_storage kk vv wT rest hdead
  | transient =>
      exfalso; obtain ⟨op, v, rfl⟩ := classify_store_shape hclass
      cases op <;> simp_all [classify, regionStoreWidth]
  | memory =>
      exfalso; obtain ⟨op, v, rfl⟩ := classify_store_shape hclass
      cases op <;> simp_all [classify, regionStoreWidth]


/-! #### Structural reduction of `dseStmts_sound` to `deadAt_sound`

Everything below is proved outright; the pass's soundness rests only on
`deadAt_sound` above. -/

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
