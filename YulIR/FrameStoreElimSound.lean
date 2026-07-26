import YulIR.FrameStoreElim
import YulIR.FrameDceSound

set_option warningAsError true
/-!
# YulIR.FrameStoreElimSound — soundness of the store/load elimination passes

Groundwork layer: the *semantics of address descriptors*. A descriptor `base + offset` denotes
`σ base + offset` (`AddrVal`); the environment `DescEnv` is a set of affine facts about the local
store (`EnvOK`), maintained by `stepEnvAssign`. On valid descriptors the two syntactic disequality
tests are semantically sound:

* `provablyNE`: same base and different offsets ⟹ the denoted addresses differ (word-granular
  spaces — `sstore`/`tstore` keys);
* `provablyDisjoint32`: same base and offset difference `δ ∈ [32, 2^256 − 32]` ⟹ the two 32-byte
  `.toNat` windows are disjoint in ℕ, for **any** value of the common base (wrap-safe).
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome BuiltinResult Literal Ident)
open YulSemantics.EVM (evm litValue stepOp EvmState)
open YulIR.FinFrame (AddrDesc DescEnv descOf rhsDesc stepEnvAssign provablyNE provablyDisjoint32)

/-! ### Denotation and validity -/

/-- The address a descriptor denotes at a local store. -/
def AddrVal (σ : Store n) (d : AddrDesc n) : U256 :=
  (match d.base with | some b => σ b | none => 0) + d.offset

/-- The descriptor environment is valid: every fact `i ↦ base + offset` is true of the store. -/
def EnvOK (σ : Store n) (env : DescEnv n) : Prop :=
  ∀ p ∈ env, σ p.1 = AddrVal σ p.2

/-- Canonicalizing an address operand preserves its value. -/
theorem descOf_sound {σ : Store n} {env} (h : EnvOK σ env) (a : Atom n) :
    AddrVal σ (descOf env a) = evalAtom σ a := by
  cases a with
  | lit l => simp [descOf, AddrVal, evalAtom]
  | slot i =>
      simp only [descOf]
      cases hf : env.find? (fun p => p.1 == i) with
      | none => simp [AddrVal, evalAtom]
      | some p =>
          have hmem := List.mem_of_find?_eq_some hf
          have hpi : p.1 = i := by simpa using List.find?_some hf
          show AddrVal σ p.2 = σ i
          rw [← hpi]
          exact (h p hmem).symm

/-! ### Semantic disequality -/

/-- `provablyNE` is sound: the denoted addresses differ. -/
theorem provablyNE_sound {σ : Store n} {d₁ d₂ : AddrDesc n}
    (h : provablyNE d₁ d₂ = true) : AddrVal σ d₁ ≠ AddrVal σ d₂ := by
  obtain ⟨hb, ho⟩ := Bool.and_eq_true_iff.mp h
  have hbase : d₁.base = d₂.base := by
    cases hd₁ : d₁.base <;> cases hd₂ : d₂.base <;> simp_all
  have hoff : d₁.offset ≠ d₂.offset := by simpa using ho
  simp only [AddrVal, hbase]
  intro hc
  exact hoff (by
    have := congrArg (· - (match d₂.base with | some b => σ b | none => 0)) hc
    simpa [BitVec.add_comm, BitVec.add_sub_cancel] using this)

/-- The word count needed to cover the 32-byte window at byte address `a` (as `activeWordsAfter`
computes it for size 32). -/
def wordsReq (a : U256) : Nat := (a.toNat + 31) / 32 + 1

/-- `provablyDisjoint32` is sound: the two 32-byte `.toNat` windows are disjoint in ℕ, whatever the
common base evaluates to. -/
theorem provablyDisjoint32_sound {σ : Store n} {d₁ d₂ : AddrDesc n}
    (h : provablyDisjoint32 d₁ d₂ = true) :
    ∀ i < 32, ∀ j < 32, (AddrVal σ d₁).toNat + i ≠ (AddrVal σ d₂).toNat + j := by
  obtain ⟨hb, hr⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hlo, hhi⟩ := Bool.and_eq_true_iff.mp hr
  have hbase : d₁.base = d₂.base := by
    cases hd₁ : d₁.base <;> cases hd₂ : d₂.base <;> simp_all
  -- name the two denoted addresses and the offset difference
  set a := AddrVal σ d₁ with ha
  set b := AddrVal σ d₂ with hbv
  have hδ : a - b = d₁.offset - d₂.offset := by
    simp only [ha, hbv, AddrVal, hbase]
    generalize (match d₂.base with | some b => σ b | none => 0) = base
    exact add_sub_add_left_eq_sub d₁.offset d₂.offset base
  have hlo' : 32 ≤ (a - b).toNat := by
    rw [hδ]
    exact BitVec.le_def.mp (by simpa using hlo)
  have hhi' : (a - b).toNat ≤ 2 ^ 256 - 32 := by
    rw [hδ]
    have := BitVec.le_def.mp (by simpa using hhi)
    calc (d₁.offset - d₂.offset).toNat ≤ ((0 : U256) - 32).toNat := this
    _ = 2 ^ 256 - 32 := by rfl
  -- a.toNat = (b + (a-b)).toNat, split on the wrap
  have hab : a = b + (a - b) := by ring
  have htoNat : a.toNat = (b.toNat + (a - b).toNat) % 2 ^ 256 := by
    conv_lhs => rw [hab]
    exact BitVec.toNat_add ..
  intro i hi j hj hc
  by_cases hwrap : b.toNat + (a - b).toNat < 2 ^ 256
  · -- no wrap: a.toNat = b.toNat + δ ≥ b.toNat + 32
    have : a.toNat = b.toNat + (a - b).toNat := by rw [htoNat]; exact Nat.mod_eq_of_lt hwrap
    omega
  · -- wrap: b.toNat - a.toNat = 2^256 - δ ≥ 32
    have hblt : b.toNat < 2 ^ 256 := b.isLt
    have hdlt : (a - b).toNat < 2 ^ 256 := (a - b).isLt
    have : a.toNat = b.toNat + (a - b).toNat - 2 ^ 256 := by
      rw [htoNat]
      omega
    omega

end YulIR.FinFrame.Sem
