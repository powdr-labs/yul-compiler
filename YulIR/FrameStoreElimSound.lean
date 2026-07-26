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

/-! ### The memory-word roundtrip (for store-to-load forwarding) -/

open YulSemantics.EVM (loadWord storeWord byteAt)
theorem getLsbD_255 (j : Nat) : (255 : BitVec 256).getLsbD j = decide (j < 8) := by
  rw [show (255 : BitVec 256) = BitVec.ofNat 256 (2 ^ 8 - 1) from rfl]
  rcases Nat.lt_or_ge j 256 with hj | hj
  · rw [show (2 ^ 8 - 1 : Nat) = 255 from rfl]
    simp only [BitVec.getLsbD_ofNat]
    rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    simp [hj]
  · rw [BitVec.getLsbD_of_ge _ _ hj]
    have : ¬ j < 8 := by omega
    simp [this]

/-- Rebuilding one byte: `(x >>> (k+8)) <<< 8 ||| (x >>> k &&& 255) = x >>> k`. -/
theorem shift_byte_step (x : BitVec 256) (k : Nat) :
    ((x >>> (k + 8)) <<< (8:Nat)) ||| ((x >>> k) &&& 255) = x >>> k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_and, getLsbD_255]
  rcases Nat.lt_or_ge (j : Nat) 8 with hj | hj
  · simp [hj]
  · rcases Nat.lt_or_ge (j : Nat) 256 with hj2 | hj2
    · have hidx : k + 8 + ((j : Nat) - 8) = k + j := by omega
      simp [hj2, Nat.not_lt.mpr hj, hidx]
    · have h1 : ¬ (j : Nat) < 256 := by omega
      have h2 : ¬ (j : Nat) < 8 := by omega
      simp [h1, h2, BitVec.getLsbD_of_ge x (k + j) (by omega)]




theorem byte_as_bv (v : U256) (k : Nat) :
    BitVec.ofNat 256 (byteAt v k).toNat = (v >>> (8 * k)) &&& 255 := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 256 (UInt8.toNat (UInt8.ofNat (v >>> (8 * k)).toNat))).toNat
      = ((v >>> (8 * k)) &&& 255).toNat
  rw [show ∀ x : Nat, UInt8.toNat (UInt8.ofNat x) = x % 2 ^ 8 from fun x => rfl]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_and]
  have h1 : (v >>> (8 * k)).toNat % 2 ^ 8 < 2 ^ 256 := by
    have := Nat.mod_lt (v >>> (8 * k)).toNat (show 0 < 2 ^ 8 by norm_num)
    omega
  rw [Nat.mod_eq_of_lt h1,
    show ((255 : U256)).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem recon_aux (v : BitVec 256) : ∀ k, k ≤ 32 →
    (List.range k).foldl
      (fun (acc : BitVec 256) (i : Nat) => acc <<< (8:Nat) ||| (v >>> (8 * (31 - i)) &&& 255))
      (0 : BitVec 256)
      = v >>> (8 * (32 - k)) := by
  intro k
  induction k with
  | zero =>
      intro _
      apply BitVec.eq_of_getLsbD_eq
      intro j
      rcases Nat.lt_or_ge (256 + j) 256 with h | h
      · omega
      · simp [BitVec.getLsbD_ushiftRight]
  | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
      rw [show 8 * (32 - k) = 8 * (31 - k) + 8 by omega]
      rw [shift_byte_step v (8 * (31 - k))]
      congr 1
      omega

theorem word_reconstruct (v : BitVec 256) :
    (List.range 32).foldl
      (fun (acc : BitVec 256) (i : Nat) => acc <<< (8:Nat) ||| (v >>> (8 * (31 - i)) &&& 255))
      (0 : BitVec 256)
      = v := by
  rw [recon_aux v 32 (Nat.le_refl _)]
  simp

/-- **Store/load roundtrip**: reading back a just-stored word yields the stored value. -/
theorem loadWord_storeWord (mem : Nat → UInt8) (p : Nat) (v : U256) :
    loadWord (storeWord mem p v) p = v := by
  have hread : ∀ acc : BitVec 256, ∀ i ∈ List.range 32,
      acc <<< (8:Nat) ||| BitVec.ofNat 256 (storeWord mem p v (p + i)).toNat
        = (acc <<< (8:Nat) ||| ((v >>> (8 * (31 - i)) &&& 255) : BitVec 256)) := by
    intro acc i hi
    rw [List.mem_range] at hi
    congr 1
    rw [show storeWord mem p v (p + i) = byteAt v (31 - i) by
      simp only [storeWord]
      rw [if_pos (by omega)]
      congr 1
      omega]
    exact byte_as_bv v (31 - i)
  unfold loadWord
  exact (List.foldl_ext _ _ _ hread).trans (word_reconstruct v)

end YulIR.FinFrame.Sem
