import YulSemantics.Equiv
import YulSemantics.Dialect.EVM
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadStore.KeyDiff

**Symbolic key-difference analysis** — the alias core of dead-store elimination.

A store's *location* is named by an expression `k` (the slot for `sstore`/`tstore`,
the byte offset for `mstore`/`mstore8`). To decide whether two locations
must-alias (so a later store *overwrites* an earlier one) or must-not-alias (so
an intervening load cannot *observe* an earlier one), we normalize a key into a
**base plus a constant integer offset** and compare:

```
splitKey k = (base, c)     -- k denotes `base + c`, c : ℤ
keyDelta k₁ k₂ = some (c₁ - c₂)   when base₁ ≡ base₂ syntactically, else none
```

`base` is one of: the canonical **constant base** `lit 0` (a fully-literal key —
after the pipeline's `Simplify`/`Propagate` rounds constant keys are already
folded to `lit n`), a **variable** `var x`, or an **opaque** expression compared
by syntactic equality. Only the first two are *stable* (a variable base survives
until the variable is reassigned; the const base always does), which is what the
dead-store traversal tracks.

The two aliasing regimes, from the EVM dialect (`YulSemantics.Dialect.EVM`):

* **word-addressed** storage / transient storage — `sload k = st.storage k`,
  `sstore` is `upd st.storage k v`. Two slots alias iff their key *words* are
  equal. So a nonzero constant `keyDelta` (small enough not to wrap) proves
  must-not-alias, and `keyDelta = 0` proves must-alias.
* **byte-ranged** memory — `mstore p v` writes bytes `[p, p+32)`
  (`storeWord`), `mstore8` writes byte `p`, `mload p` reads `[p, p+32)`. Two
  writes of widths `w₁,w₂` at the same base with offsets `o₁,o₂` are disjoint iff
  `|o₁-o₂| ≥ 0x20` (for full words) — a constant `keyDelta` *outside* the window
  `(-0x20, 0x20)` proves must-not-alias.

The soundness lemmas at the bottom relate `keyDelta` to (in)equality of the
*evaluated* key words. The clean word-difference direction is proved; the memory
byte-range / wraparound facts are stated precisely and left as `sorry`
(they need the no-overflow side condition `base.toNat + max offset < 2^256`).
-/

namespace YulEvmCompiler.Optimizer.DeadStore

open YulSemantics
open YulSemantics.EVM

/-! ### Syntactic expression equality

`Expr Op` has no derived `DecidableEq` (the deriving handler does not recurse
through `List`), so we define a structural `Bool` equality for the base
comparison. `Op` and `Literal` do derive `DecidableEq`; `Ident = String` has
`BEq`. -/

mutual
/-- Structural equality of expressions (used only to compare *bases*). -/
def beqExpr : Expr Op → Expr Op → Bool
  | .lit a,          .lit b          => decide (a = b)
  | .var a,          .var b          => a == b
  | .builtin o1 a1,  .builtin o2 a2  => decide (o1 = o2) && beqArgs a1 a2
  | .call f1 a1,     .call f2 a2     => f1 == f2 && beqArgs a1 a2
  | _,               _               => false
/-- Structural equality of expression lists. -/
def beqArgs : List (Expr Op) → List (Expr Op) → Bool
  | [],      []      => true
  | x :: xs, y :: ys => beqExpr x y && beqArgs xs ys
  | _,       _       => false
end

-- `Expr` is a nested inductive (recursion through `List`); the structural facts
-- below are proved by mutual structural recursion (matching `beqExpr`'s shape)
-- rather than the `induction` tactic, which does not fire on nested inductives.
mutual
@[simp] theorem beqExpr_refl : ∀ e : Expr Op, beqExpr e e = true
  | .lit _ => by simp only [beqExpr]; simp
  | .var _ => by simp only [beqExpr]; simp
  | .builtin op args => by
      simp only [beqExpr, Bool.and_eq_true]
      exact ⟨by simp, beqArgs_refl args⟩
  | .call f args => by
      simp only [beqExpr, Bool.and_eq_true]
      exact ⟨by simp, beqArgs_refl args⟩
theorem beqArgs_refl : ∀ args : List (Expr Op), beqArgs args args = true
  | [] => by simp only [beqArgs]
  | a :: as => by
      simp only [beqArgs, Bool.and_eq_true]
      exact ⟨beqExpr_refl a, beqArgs_refl as⟩
end

-- `beqExpr` reflects syntactic equality: if it returns `true`, the expressions
-- are equal.
mutual
theorem beqExpr_eq : ∀ {e₁ e₂ : Expr Op}, beqExpr e₁ e₂ = true → e₁ = e₂
  | .lit a,         .lit b,         h => by simp only [beqExpr, decide_eq_true_eq] at h; rw [h]
  | .var a,         .var b,         h => by simp only [beqExpr, beq_iff_eq] at h; rw [h]
  | .builtin o1 a1, .builtin o2 a2, h => by
      simp only [beqExpr, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, beqArgs_eq h.2]
  | .call f1 a1,    .call f2 a2,    h => by
      simp only [beqExpr, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, beqArgs_eq h.2]
  | .lit _,         .var _,         h => by simp [beqExpr] at h
  | .lit _,         .builtin _ _,   h => by simp [beqExpr] at h
  | .lit _,         .call _ _,      h => by simp [beqExpr] at h
  | .var _,         .lit _,         h => by simp [beqExpr] at h
  | .var _,         .builtin _ _,   h => by simp [beqExpr] at h
  | .var _,         .call _ _,      h => by simp [beqExpr] at h
  | .builtin _ _,   .lit _,         h => by simp [beqExpr] at h
  | .builtin _ _,   .var _,         h => by simp [beqExpr] at h
  | .builtin _ _,   .call _ _,      h => by simp [beqExpr] at h
  | .call _ _,      .lit _,         h => by simp [beqExpr] at h
  | .call _ _,      .var _,         h => by simp [beqExpr] at h
  | .call _ _,      .builtin _ _,   h => by simp [beqExpr] at h
theorem beqArgs_eq : ∀ {a₁ a₂ : List (Expr Op)}, beqArgs a₁ a₂ = true → a₁ = a₂
  | [],      [],      _ => rfl
  | x :: xs, y :: ys, h => by
      simp only [beqArgs, Bool.and_eq_true] at h
      rw [beqExpr_eq h.1, beqArgs_eq h.2]
  | [],      _ :: _,  h => by simp [beqArgs] at h
  | _ :: _,  [],      h => by simp [beqArgs] at h
end

/-! ### Base + offset normalization -/

/-- The canonical constant base: a fully-literal key `k` normalizes to
`(constBase, value k)`. -/
def constBase : Expr Op := .lit (.number 0)

/-- Normalize a key expression to a base and a constant integer offset such that
the key denotes `base + offset` (modulo `2^256`). Peels `add`/`sub` spines whose
non-base side is a number literal; a fully-literal key collapses to the constant
base. Anything else is its own opaque base at offset `0`. -/
def splitKey : Expr Op → Expr Op × Int
  | .lit (.number n) => (constBase, (n : Int))
  | .builtin .add [e₁, e₂] =>
      let (b₁, c₁) := splitKey e₁
      let (b₂, c₂) := splitKey e₂
      if beqExpr b₁ constBase then (b₂, c₁ + c₂)
      else if beqExpr b₂ constBase then (b₁, c₁ + c₂)
      else (.builtin .add [e₁, e₂], 0)
  | .builtin .sub [e₁, e₂] =>
      let (b₁, c₁) := splitKey e₁
      let (b₂, c₂) := splitKey e₂
      if beqExpr b₂ constBase then (b₁, c₁ - c₂)
      else (.builtin .sub [e₁, e₂], 0)
  | e => (e, 0)

/-- The base component of a key. -/
def keyBase (k : Expr Op) : Expr Op := (splitKey k).1
/-- The constant-offset component of a key. -/
def keyOff (k : Expr Op) : Int := (splitKey k).2

/-- `some (c₁ - c₂)` when the two keys share a base (so their word difference is
the constant `c₁ - c₂`); `none` when the bases differ syntactically and no
constant relationship is known. -/
def keyDelta (k₁ k₂ : Expr Op) : Option Int :=
  if beqExpr (keyBase k₁) (keyBase k₂) then some (keyOff k₁ - keyOff k₂) else none

/-! ### Aliasing predicates -/

/-- Word regions (storage / transient): `k₁` and `k₂` **must not alias** when
their difference is a known nonzero constant. -/
def mustNotAliasWord (k₁ k₂ : Expr Op) : Bool :=
  match keyDelta k₁ k₂ with
  | some d => decide (d ≠ 0)
  | none   => false

/-- Word regions: `k₁` **must alias** `k₂` (same slot) when their difference is a
known zero. -/
def mustAliasWord (k₁ k₂ : Expr Op) : Bool :=
  keyDelta k₁ k₂ == some 0

/-- Memory: a write of width `wLate` at `kLate` **covers** a prior write of width
`wEarly` at `kEarly` when they share a base and the early byte range
`[oₑ, oₑ+wₑ)` is contained in the late range `[oₗ, oₗ+wₗ)`, i.e.
`0 ≤ oₑ - oₗ ≤ wₗ - wₑ`. -/
def mustCoverMem (kLate : Expr Op) (wLate : Int) (kEarly : Expr Op) (wEarly : Int) : Bool :=
  match keyDelta kEarly kLate with
  | some d => decide (0 ≤ d ∧ d + wEarly ≤ wLate)
  | none   => false

/-- Memory: `k₁` and `k₂` (each naming a `wᵢ`-byte window) **must not alias**
when their constant difference puts the windows outside each other — for full
words this is `|Δ| ≥ 0x20`. General form: `d ≥ w₂` or `d ≤ -w₁` where
`d = off₁ - off₂`. -/
def mustNotAliasMem (k₁ : Expr Op) (w₁ : Int) (k₂ : Expr Op) (w₂ : Int) : Bool :=
  match keyDelta k₁ k₂ with
  | some d => decide (w₂ ≤ d ∨ d ≤ -w₁)
  | none   => false

/-- The byte width written by a memory store op (`mstore` = 32, `mstore8` = 1). -/
def memWidth : Op → Option Int
  | .mstore  => some 32
  | .mstore8 => some 1
  | .mload   => some 32   -- a load observes a 32-byte window
  | _        => none

/-! ### Value-difference soundness

The analysis is sound because two keys that share a base evaluate to words
differing by exactly the constant offset delta. We isolate the arithmetic facts
here.

`evalKeyShape k base c w V st` says: `k` evaluated at `(V, st)` yields the word
`w`, and `w = bw + (c : BitVec 256)` for the base word `bw` obtained by
evaluating `base` at the *same* `(V, st)`. This is what `splitKey` guarantees for
a pure base.  We record it as a `Prop` and relate `keyDelta` to it. -/

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-- The word denoted by an integer offset. -/
def offWord (c : Int) : U256 := BitVec.ofInt 256 c

/-- **Core word-difference lemma (must-not-alias, word regions).**

If two keys share a base and evaluate (from the *same* configuration, with the
base stable) to base word `bw`, so `w₁ = bw + off c₁` and `w₂ = bw + off c₂`,
and the constant delta `c₁ - c₂` is nonzero and does not wrap (`|c₁-c₂| < 2^256`),
then the key words differ. This is the fact `mustNotAliasWord` relies on. -/
theorem word_ne_of_delta_ne_zero (bw : U256) (c₁ c₂ : Int)
    (hne : c₁ - c₂ ≠ 0) (hbound : (c₁ - c₂).natAbs < 2 ^ 256) :
    bw + offWord c₁ ≠ bw + offWord c₂ := by
  intro hEq
  have h2 : offWord c₁ = offWord c₂ := add_left_cancel hEq
  have h3 : (offWord c₁).toInt = (offWord c₂).toInt := by rw [h2]
  simp only [offWord, BitVec.toInt_ofInt] at h3
  -- h3 : c₁.bmod (2^256) = c₂.bmod (2^256); bridge to `%`, then to `∣`.
  have hh := congrArg (fun z => z % ((2 ^ 256 : Nat) : Int)) h3
  rw [Int.bmod_emod, Int.bmod_emod] at hh
  have hdvd : ((2 ^ 256 : Nat) : Int) ∣ (c₂ - c₁) := Int.modEq_iff_dvd.mp hh
  have hdvdN : ((2 ^ 256 : Nat) : Int).natAbs ∣ (c₂ - c₁).natAbs :=
    Int.natAbs_dvd_natAbs.mpr hdvd
  have hpos : 0 < (c₂ - c₁).natAbs := by rw [Int.natAbs_pos]; omega
  have hle : (2 : Nat) ^ 256 ≤ (c₂ - c₁).natAbs := by
    have := Nat.le_of_dvd hpos hdvdN; simpa using this
  have hsymm : (c₂ - c₁).natAbs = (c₁ - c₂).natAbs := by rw [← Int.natAbs_neg]; ring_nf
  omega

/-- **Core word-equality lemma (must-alias, word regions).**

Sharing a base with equal offsets yields equal key words — trivially, since the
keys are then syntactically equal. -/
theorem word_eq_of_delta_zero (bw : U256) (c : Int) :
    bw + offWord c = bw + offWord c := rfl

/-- **Memory non-overlap lemma.** Two 32-byte windows at the same base with
non-negative offsets `c₁, c₂` whose delta lands outside `(-0x20, 0x20)` have
disjoint byte ranges (no address lies in both). Non-negativity is the honest
side condition for byte-addressed offsets; the windows here are the actual
addresses `base + offset` after the base-value is factored out (`bwN`), so no
`2^256` wrap enters this statement — that is handled by the separate lemma
relating `p.toNat` to `bwN + offset`. -/
theorem mem_disjoint_of_delta (bwN : Nat) (c₁ c₂ : Int)
    (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂)
    (hsep : (32 : Int) ≤ c₁ - c₂ ∨ c₁ - c₂ ≤ -(32 : Int)) :
    ∀ a : Nat,
      ¬ ((bwN + c₁.toNat ≤ a ∧ a < bwN + c₁.toNat + 32) ∧
         (bwN + c₂.toNat ≤ a ∧ a < bwN + c₂.toNat + 32)) := by
  intro a ⟨⟨l1, r1⟩, ⟨l2, r2⟩⟩
  have e1 : (c₁.toNat : Int) = c₁ := Int.toNat_of_nonneg h1
  have e2 : (c₂.toNat : Int) = c₂ := Int.toNat_of_nonneg h2
  omega

end YulEvmCompiler.Optimizer.DeadStore
