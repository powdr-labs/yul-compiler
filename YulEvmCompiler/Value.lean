import EvmSemantics.Data.UInt256
import YulSemantics.Dialect.EVM

/-!
# YulEvmCompiler.Value

The value conversion between the two word types:

* yul-semantics: `YulSemantics.EVM.U256 := BitVec 256`
* evm-semantics: `EvmSemantics.UInt256` (a wrapper over `Fin (2^256)`)

`conv` is the evident bijection, and this file proves one agreement lemma per
supported built-in: applying the yul-semantics value operation and converting
equals converting and applying the evm-semantics operation. These lemmas are
the entire number-theoretic content of the compiler proof; each is independent,
and an op enters the compiler's supported set exactly when its lemma exists.
-/

namespace YulEvmCompiler

open YulSemantics.EVM (U256 b2w)

/-- Convert a yul-semantics word (`BitVec 256`) to an evm-semantics word
(`Fin (2^256)` wrapper). -/
def conv (v : U256) : EvmSemantics.UInt256 := ⟨⟨v.toNat, v.isLt⟩⟩

@[simp] theorem conv_toNat (v : U256) : (conv v).toNat = v.toNat := rfl

theorem u256ext {a b : EvmSemantics.UInt256} (h : a.toNat = b.toNat) :
    a = b := by
  cases a; cases b
  exact congrArg EvmSemantics.UInt256.mk (Fin.ext h)

theorem conv_injective : Function.Injective conv := by
  intro a b h
  have : a.toNat = b.toNat := congrArg EvmSemantics.UInt256.toNat h
  exact BitVec.toNat_injective this

@[simp] theorem conv_inj {a b : U256} : conv a = conv b ↔ a = b :=
  conv_injective.eq_iff

theorem toNat_u256_ofNat (n : Nat) :
    (EvmSemantics.UInt256.ofNat n).toNat = n % 2 ^ 256 := by
  simp [EvmSemantics.UInt256.ofNat, EvmSemantics.UInt256.toNat, Fin.ofNat,
    EvmSemantics.UInt256.size]

theorem conv_eq_ofNat (v : U256) : conv v = EvmSemantics.UInt256.ofNat v.toNat := by
  apply u256ext
  rw [toNat_u256_ofNat, conv_toNat, Nat.mod_eq_of_lt v.isLt]

@[simp] theorem conv_zero : conv 0 = ⟨0⟩ := rfl

private theorem toNat_ne_zero {b : U256} (hb : b ≠ 0) : b.toNat ≠ 0 := by
  intro h
  exact hb (BitVec.toNat_injective (by simpa using h))

/-!
## Per-op agreement lemmas

One lemma per supported built-in: the left-hand side is (the value part of)
yul-semantics' `stepOp` arm, the right-hand side the expression the matching
`EvmSemantics.EVM.StepRunning` rule pushes. Operand order follows the rules:
the yul `bin f` helper receives `[a, b]` with `a` the *first* Yul argument,
which the compiler arranges to be the EVM stack top.
-/

open EvmSemantics (UInt256)

theorem conv_add (a b : U256) : conv (a + b) = conv a + conv b := by
  apply u256ext
  show (a + b).toNat = ((conv a).val + (conv b).val).val
  rw [BitVec.toNat_add, Fin.val_add]
  rfl

theorem conv_sub (a b : U256) : conv (a - b) = conv a - conv b := by
  apply u256ext
  show (a - b).toNat = ((conv a).val - (conv b).val).val
  rw [BitVec.toNat_sub, Fin.val_sub]
  rfl

theorem conv_mul (a b : U256) : conv (a * b) = conv a * conv b := by
  apply u256ext
  show (a * b).toNat = ((conv a).val * (conv b).val).val
  rw [BitVec.toNat_mul, Fin.val_mul]
  rfl

theorem conv_div (a b : U256) :
    conv (if b = 0 then 0 else a / b) = conv a / conv b := by
  apply u256ext
  show _ = (UInt256.div (conv a) (conv b)).toNat
  unfold UInt256.div
  by_cases hb : b = 0
  · subst hb
    rfl
  · rw [if_neg hb,
      if_neg (show ¬(((conv b).val : Nat) = 0) from fun hc => toNat_ne_zero hb hc)]
    show (a / b).toNat = a.toNat / b.toNat
    exact BitVec.toNat_udiv

theorem conv_mod (a b : U256) :
    conv (if b = 0 then 0 else a % b) = conv a % conv b := by
  apply u256ext
  show _ = (UInt256.mod (conv a) (conv b)).toNat
  unfold UInt256.mod
  by_cases hb : b = 0
  · subst hb
    rfl
  · rw [if_neg hb,
      if_neg (show ¬(((conv b).val : Nat) = 0) from fun hc => toNat_ne_zero hb hc)]
    show (a % b).toNat = a.toNat % b.toNat
    exact BitVec.toNat_umod

theorem conv_addmod (a b n : U256) :
    conv (if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % n.toNat))
      = UInt256.addMod (conv a) (conv b) (conv n) := by
  apply u256ext
  unfold UInt256.addMod
  by_cases hn : n = 0
  · subst hn
    rfl
  · rw [if_neg hn,
      if_neg (show ¬(((conv n).val : Nat) = 0) from fun hc => toNat_ne_zero hn hc)]
    simp only [conv_toNat, BitVec.toNat_ofNat, toNat_u256_ofNat]

theorem conv_mulmod (a b n : U256) :
    conv (if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % n.toNat))
      = UInt256.mulMod (conv a) (conv b) (conv n) := by
  apply u256ext
  unfold UInt256.mulMod
  by_cases hn : n = 0
  · subst hn
    rfl
  · rw [if_neg hn,
      if_neg (show ¬(((conv n).val : Nat) = 0) from fun hc => toNat_ne_zero hn hc)]
    simp only [conv_toNat, BitVec.toNat_ofNat, toNat_u256_ofNat]

theorem conv_exp (a b : U256) :
    conv (BitVec.ofNat 256 (a.toNat ^ b.toNat)) = UInt256.exp (conv a) (conv b) := by
  apply u256ext
  unfold UInt256.exp
  simp only [conv_toNat, BitVec.toNat_ofNat, toNat_u256_ofNat]
  show _ = _ % EvmSemantics.UInt256.size % 2 ^ 256
  rw [show EvmSemantics.UInt256.size = 2 ^ 256 from rfl, Nat.mod_mod]

theorem conv_clz (a : U256) :
    conv (YulSemantics.EVM.clzVal a) = UInt256.clz (conv a) := by
  apply u256ext
  unfold YulSemantics.EVM.clzVal UInt256.clz
  by_cases ha : a = 0
  · subst ha
    rfl
  · rw [if_neg ha,
      if_neg (show ¬((conv a).toNat = 0) from toNat_ne_zero ha)]
    simp only [conv_toNat, BitVec.toNat_ofNat, toNat_u256_ofNat]

private theorem conv_bool (c : Bool) :
    conv (b2w c) = if c then UInt256.ofNat 1 else UInt256.ofNat 0 := by
  cases c
  · apply u256ext
    simp [YulSemantics.EVM.b2w, toNat_u256_ofNat]
  · apply u256ext
    simp [YulSemantics.EVM.b2w, toNat_u256_ofNat]

theorem conv_lt (a b : U256) :
    conv (b2w (a.ult b)) = UInt256.lt (conv a) (conv b) := by
  rw [conv_bool]
  unfold UInt256.lt
  simp only [conv_toNat]
  by_cases h : a.toNat < b.toNat
  · rw [if_pos (by simp [BitVec.ult, h]), if_pos h]
  · rw [if_neg (by simp [BitVec.ult, h]), if_neg h]

theorem conv_gt (a b : U256) :
    conv (b2w (b.ult a)) = UInt256.gt (conv a) (conv b) := by
  rw [conv_bool]
  unfold UInt256.gt
  simp only [conv_toNat]
  by_cases h : b.toNat < a.toNat
  · rw [if_pos (by simp [BitVec.ult, h]), if_pos h]
  · rw [if_neg (by simp [BitVec.ult, h]), if_neg h]

private theorem toSignedNat_conv (a : U256) :
    (conv a).toSignedNat = a.toInt := by
  unfold UInt256.toSignedNat
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [conv_toNat]
  have h2 : (2 : Nat) ^ 256 = 2 * 2 ^ 255 := by
    rw [show (256 : Nat) = 255 + 1 from rfl, Nat.pow_succ]
    ring
  have hhalf : EvmSemantics.UInt256.size / 2 = 2 ^ 255 := by
    show 2 ^ 256 / 2 = _
    rw [h2]
    omega
  rw [hhalf]
  by_cases h : a.toNat < 2 ^ 255
  · rw [if_pos h, if_pos (by rw [h2]; omega)]
  · rw [if_neg h, if_neg (by rw [h2]; omega)]
    show (a.toNat : Int) - (EvmSemantics.UInt256.size : Nat) = _
    rw [show EvmSemantics.UInt256.size = 2 ^ 256 from rfl]

theorem conv_slt (a b : U256) :
    conv (b2w (a.slt b)) = UInt256.slt (conv a) (conv b) := by
  rw [conv_bool]
  unfold UInt256.slt
  by_cases h : a.toInt < b.toInt
  · rw [if_pos (by simp [BitVec.slt, h]),
      if_pos (by rw [toSignedNat_conv, toSignedNat_conv]; exact h)]
  · rw [if_neg (by simp [BitVec.slt, h]),
      if_neg (by rw [toSignedNat_conv, toSignedNat_conv]; exact h)]

theorem conv_sgt (a b : U256) :
    conv (b2w (b.slt a)) = UInt256.sgt (conv a) (conv b) := by
  rw [conv_bool]
  unfold UInt256.sgt
  by_cases h : b.toInt < a.toInt
  · rw [if_pos (by simp [BitVec.slt, h]),
      if_pos (show (conv a).toSignedNat > (conv b).toSignedNat from by
        rw [toSignedNat_conv, toSignedNat_conv]; exact h)]
  · rw [if_neg (by simp [BitVec.slt, h]),
      if_neg (show ¬(conv a).toSignedNat > (conv b).toSignedNat from by
        rw [toSignedNat_conv, toSignedNat_conv]; exact h)]

theorem conv_eq (a b : U256) :
    conv (b2w (a = b)) = UInt256.eq (conv a) (conv b) := by
  rw [conv_bool]
  unfold UInt256.eq
  simp only [conv_toNat]
  by_cases h : a = b
  · rw [if_pos (decide_eq_true h), if_pos (congrArg BitVec.toNat h)]
  · rw [if_neg (by simp [h]), if_neg (fun hc => h (BitVec.toNat_injective hc))]

theorem conv_iszero (a : U256) :
    conv (b2w (a = 0)) = UInt256.isZero (conv a) := by
  rw [conv_bool]
  unfold UInt256.isZero
  simp only [conv_toNat]
  by_cases h : a = 0
  · rw [if_pos (decide_eq_true h), if_pos (by simp [h])]
  · rw [if_neg (by simpa using h), if_neg (toNat_ne_zero h)]

theorem conv_and (a b : U256) :
    conv (a &&& b) = UInt256.land (conv a) (conv b) := by
  apply u256ext
  show (a &&& b).toNat = Nat.land a.toNat b.toNat % 2 ^ 256
  rw [BitVec.toNat_and]
  exact (Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ b.isLt)).symm

theorem conv_or (a b : U256) :
    conv (a ||| b) = UInt256.lor (conv a) (conv b) := by
  apply u256ext
  show (a ||| b).toNat = Nat.lor a.toNat b.toNat % 2 ^ 256
  rw [BitVec.toNat_or]
  exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow a.isLt b.isLt)).symm

theorem conv_xor (a b : U256) :
    conv (a ^^^ b) = UInt256.xor (conv a) (conv b) := by
  apply u256ext
  show (a ^^^ b).toNat = Nat.xor a.toNat b.toNat % 2 ^ 256
  rw [BitVec.toNat_xor]
  exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.isLt b.isLt)).symm

theorem conv_not (a : U256) :
    conv (~~~a) = UInt256.lnot (conv a) := by
  apply u256ext
  unfold UInt256.lnot
  simp only [conv_toNat]
  rw [BitVec.toNat_not, toNat_u256_ofNat]
  show 2 ^ 256 - 1 - a.toNat = (EvmSemantics.UInt256.size - 1 - a.toNat) % 2 ^ 256
  rw [show EvmSemantics.UInt256.size = 2 ^ 256 from rfl]
  have := a.isLt
  omega

theorem conv_byte (i x : U256) :
    conv (if 32 ≤ i.toNat then 0 else (x >>> (248 - 8 * i.toNat)) &&& 0xff)
      = UInt256.byteAt (conv i) (conv x) := by
  apply u256ext
  unfold UInt256.byteAt
  by_cases h : 32 ≤ i.toNat
  · rw [if_pos h, if_pos (show (conv i).toNat ≥ 32 from h)]
    rfl
  · rw [if_neg h, if_neg (show ¬(conv i).toNat ≥ 32 from h)]
    show ((x >>> (248 - 8 * i.toNat)) &&& 0xff).toNat = _
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, toNat_u256_ofNat]
    simp only [conv_toNat]
    rw [show (248 - 8 * i.toNat) = 8 * (31 - i.toNat) from by omega]
    rw [show ((0xff : U256)).toNat = 0xff from rfl]
    have hle : x.toNat >>> (8 * (31 - i.toNat)) &&& 0xff ≤ 0xff := Nat.and_le_right
    rw [Nat.mod_eq_of_lt (by omega)]

theorem conv_shl (shift v : U256) :
    conv (v <<< shift.toNat) = UInt256.shiftLeft (conv v) (conv shift) := by
  apply u256ext
  unfold UInt256.shiftLeft
  by_cases h : shift.toNat ≥ 256
  · rw [if_pos (show (conv shift).toNat ≥ 256 from h)]
    show (v <<< shift.toNat).toNat = 0
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have hdvd : (2 : Nat) ^ 256 ∣ v.toNat * 2 ^ shift.toNat :=
      Dvd.dvd.mul_left (pow_dvd_pow 2 h) v.toNat
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd
  · rw [if_neg (show ¬(conv shift).toNat ≥ 256 from h)]
    simp only [conv_toNat, BitVec.toNat_shiftLeft, toNat_u256_ofNat]
    show _ = v.toNat <<< shift.toNat % EvmSemantics.UInt256.size % 2 ^ 256
    rw [show EvmSemantics.UInt256.size = 2 ^ 256 from rfl, Nat.mod_mod]

theorem conv_shr (shift v : U256) :
    conv (v >>> shift.toNat) = UInt256.shiftRight (conv v) (conv shift) := by
  apply u256ext
  unfold UInt256.shiftRight
  by_cases h : shift.toNat ≥ 256
  · rw [if_pos (show (conv shift).toNat ≥ 256 from h)]
    show (v >>> shift.toNat).toNat = 0
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt
      (lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega) h))
  · rw [if_neg (show ¬(conv shift).toNat ≥ 256 from h)]
    show (v >>> shift.toNat).toNat = v.toNat >>> shift.toNat % 2 ^ 256
    rw [BitVec.toNat_ushiftRight]
    rw [Nat.mod_eq_of_lt
      (lt_of_le_of_lt (Nat.shiftRight_le _ _) v.isLt)]

/-! ### Signed operations (`sdiv`, `smod`, `sar`, `signextend`)

Bridged through `BitVec.toInt` ↔ evm-semantics' `toSignedNat`/`ofSignedInt`.
The two representations of a signed 256-bit word agree, and each signed op is
`BitVec.ofInt` of the corresponding `Int` operation on the signed views. -/

open EvmSemantics (UInt256)

/-- evm-semantics' signed reading of a converted word is the `BitVec.toInt`. -/
theorem conv_toSignedNat (a : U256) : (conv a).toSignedNat = a.toInt := by
  have hs : UInt256.size = 2 ^ 256 := rfl
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [UInt256.toSignedNat, conv_toNat, hs]
  split_ifs with h1 h2 <;> first | rfl | omega

/-- `ofSignedInt` factors through `BitVec.ofInt` and `conv`. -/
theorem conv_ofSignedInt (z : Int) :
    UInt256.ofSignedInt z = conv (BitVec.ofInt 256 z) := by
  apply u256ext
  rw [conv_toNat, BitVec.toNat_ofInt]
  unfold UInt256.ofSignedInt
  show (UInt256.ofNat ((z % (UInt256.size : Int)).toNat)).toNat = _
  rw [toNat_u256_ofNat]
  have hsize : (UInt256.size : Int) = ((2 ^ 256 : Nat) : Int) := rfl
  rw [hsize]
  have hlt : (z % ((2 ^ 256 : Nat) : Int)).toNat < 2 ^ 256 := by
    have hpos : (0 : Int) < ((2 ^ 256 : Nat) : Int) := by positivity
    have := Int.emod_lt_of_pos z hpos
    have hnn := Int.emod_nonneg z (ne_of_gt hpos)
    omega
  rw [Nat.mod_eq_of_lt hlt]

/-- `BitVec.ofInt` only sees its argument modulo `2 ^ 256`, so `bmod` is
invisible to it. -/
private theorem ofInt_bmod (z : Int) :
    BitVec.ofInt 256 (z.bmod (2 ^ 256)) = BitVec.ofInt 256 z := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, Int.bmod_emod]

theorem conv_sdiv (a b : U256) :
    conv (if b = 0 then 0 else BitVec.sdiv a b) = UInt256.sdiv (conv a) (conv b) := by
  unfold UInt256.sdiv
  by_cases hb : b = 0
  · subst hb; rfl
  · rw [if_neg hb, if_neg (show ¬(conv b).toNat = 0 from fun hc => toNat_ne_zero hb hc),
      conv_toSignedNat, conv_toSignedNat, conv_ofSignedInt]
    congr 1
    rw [← BitVec.ofInt_toInt (x := BitVec.sdiv a b), BitVec.toInt_sdiv, ofInt_bmod]

theorem conv_smod (a b : U256) :
    conv (if b = 0 then 0 else BitVec.srem a b) = UInt256.smod (conv a) (conv b) := by
  unfold UInt256.smod
  by_cases hb : b = 0
  · subst hb; rfl
  · rw [if_neg hb, if_neg (show ¬(conv b).toNat = 0 from fun hc => toNat_ne_zero hb hc),
      conv_toSignedNat, conv_toSignedNat, conv_ofSignedInt]
    congr 1
    rw [← BitVec.ofInt_toInt (x := BitVec.srem a b), BitVec.toInt_srem]

/-- `conv` of a word is `ofSignedInt` of its signed value. -/
theorem conv_eq_ofSignedInt (w : U256) : conv w = UInt256.ofSignedInt w.toInt := by
  rw [conv_ofSignedInt, BitVec.ofInt_toInt]

/-- `ofSignedInt 0` is the zero word. -/
private theorem ofSignedInt_zero : UInt256.ofSignedInt 0 = ⟨0⟩ := rfl

theorem conv_sar (shift val : U256) :
    conv (BitVec.sshiftRight val shift.toNat)
      = UInt256.sar (conv val) (conv shift) := by
  rw [conv_eq_ofSignedInt, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  unfold UInt256.sar
  simp only [conv_toSignedNat, conv_toNat, Nat.cast_pow, Nat.cast_ofNat]
  by_cases h : shift.toNat ≥ 256
  · rw [if_pos h]
    have hlt : val.toInt < 2 ^ 255 := BitVec.toInt_lt
    have hge : -2 ^ 255 ≤ val.toInt := BitVec.le_toInt val
    have hpow : (2 : Int) ^ 255 < 2 ^ shift.toNat :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    by_cases hneg : val.toInt < 0
    · rw [if_pos hneg]
      congr 1
      rw [Int.ediv_eq_neg_one_of_neg_of_le hneg (by omega)]
    · rw [if_neg hneg]
      rw [Int.ediv_eq_zero_of_lt (by omega) (by omega), ofSignedInt_zero]
  · rw [if_neg h]

end YulEvmCompiler
