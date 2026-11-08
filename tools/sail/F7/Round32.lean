import F7.RoundQ

/-!
The lemmas on binary32 words that the proofs of the 32-bit functions share: the unpacking of a
word, the processing of NaNs, and the rounding of FPRoundBase__1 at 32 bits under FPCR
0x02000000.

`fpUnpack_run32` and `fpProcessNaNs_run32` state what FPUnpack__1 and FPProcessNaNs__1 return on
32-bit operands, as `fpUnpack_run` and `fpProcessNaNs_run` of `F7/Base.lean` state it on 64-bit
ones.  `fpRound32_q` states what FPRound__2 returns on the rational `±(P/Q) · 2^-149` for all
positive naturals `P` and `Q`: Talos's `IEEE32.roundRationalMagnitude neg P Q` and the FPSR bits
of `maskQ32 P Q`.  Its proof follows `fpRound_q` of `F7/RoundQ.lean` with the binary32 constants:
for a normal result with `log2 ⌊P/Q⌋ = 23 + j`, the loops give the exponent `j − 126`, the integer
mantissa is the quotient of `P` by `Q · 2^j`, and the error is the remainder over `Q · 2^j`; for a
subnormal one the divisor is `Q`.  An inexact subnormal result sets FPSR.UFC, since FPRoundBase__1
detects tininess before rounding.

Talos's other binary32 rounders are instances of the rational one.  `rsm_eq_rrm32` states that
`roundScaledMagnitude neg N`, the rounder of a sum and of an integer conversion, is
`roundRationalMagnitude neg N 1`, and `rdm_eq_rrm32` that `roundDyadicMagnitude neg N X`, the
rounder of a product, is `roundRationalMagnitude neg N (2^X)`.  The statements write Talos's word
as `(roundRationalMagnitude neg P Q).toBitVec` without a definition in between, for the reason
that `F7/RoundQ.lean` gives.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

/-! ## Words and unpacking -/

/-- The fields of a binary32 word, as Talos computes them. -/
def ex32 (x : BitVec 32) : Nat := x.toNat / 2 ^ 23 % 2 ^ 8
def fr32 (x : BitVec 32) : Nat := x.toNat % 2 ^ 23
def sg32 (x : BitVec 32) : Bool := decide (2 ^ 31 ≤ x.toNat)

theorem ex32_eq (x : BitVec 32) : (Sail.BitVec.extractLsb x 30 23).toNat = ex32 x := by
  simp [Sail.BitVec.extractLsb, ex32, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]

theorem fr32_eq (x : BitVec 32) : (Sail.BitVec.extractLsb x 22 0).toNat = fr32 x := by
  simp [Sail.BitVec.extractLsb, fr32, BitVec.extractLsb_toNat]

def sgBit32 (x : BitVec 32) : BitVec 1 := if sg32 x then 1#1 else 0#1

theorem sign_join32 (x : BitVec 32) : BitVec.join1 [BitVec.access x 31] = sgBit32 x := by
  rw [join1_access x 31 (by decide)]
  have := x.isLt
  unfold sgBit32 sg32
  by_cases h : 2 ^ 31 ≤ x.toNat
  · rw [ite_eq_left (by omega), decide_eq_true h]; rfl
  · rw [ite_eq_right (by omega), decide_eq_false h]; rfl

theorem qbit32 (x : BitVec 32) :
    (BitVec.join1 [BitVec.access (Sail.BitVec.extractLsb x 22 0) 22] == 1#1) =
      decide (2 ^ 22 ≤ fr32 x) := by
  rw [join1_access _ 22 (by decide), fr32_eq]
  have : fr32 x < 2 ^ 23 := Nat.mod_lt _ (by decide)
  by_cases h : 2 ^ 22 ≤ fr32 x
  · rw [ite_eq_left (by omega), decide_eq_true h]; rfl
  · rw [ite_eq_right (by omega), decide_eq_false h]; rfl

theorem denorm_val32 (f : ℕ) :
    (2 : ℝ) ^ (-126 : ℤ) * (((f : ℤ) : ℝ) * (2 : ℝ) ^ (-23 : ℤ)) =
      ((f : ℤ) : ℝ) * (2 : ℝ) ^ (-149 : ℤ) := by
  rw [show (-149 : ℤ) = -126 + -23 by norm_num, zpow_add₀ two_ne_zero]
  ring

theorem t_sign32 (x : BitVec 32) : Wasm.IEEE32.sign (UInt32.ofBitVec x) = sg32 x := by
  simp [Wasm.IEEE32.sign, sg32]
theorem t_exp32 (x : BitVec 32) : Wasm.IEEE32.exponent (UInt32.ofBitVec x) = ex32 x := by
  simp [Wasm.IEEE32.exponent, ex32]
theorem t_frac32 (x : BitVec 32) : Wasm.IEEE32.fraction (UInt32.ofBitVec x) = fr32 x := by
  simp [Wasm.IEEE32.fraction, fr32]

theorem pow_normal32 (e : ℕ) (he : e ≠ 0) :
    (2 : ℝ) ^ ((e : ℤ) - 127) = 8388608 * 2 ^ (e - 1) * (2 ^ 149)⁻¹ := by
  rw [show ((e : ℤ) - 127) = ((e - 1 : ℕ) : ℤ) - 149 + 23 by omega, zpow_add₀ two_ne_zero,
    zpow_sub₀ two_ne_zero]
  simp only [zpow_natCast, zpow_ofNat, div_eq_mul_inv]
  ring

theorem val_normal32 (e : ℕ) (he : e ≠ 0) (f : ℝ) :
    (2 : ℝ) ^ ((e : ℤ) - 127) * (1 + f * (2 ^ 23)⁻¹) =
      (8388608 + f) * 2 ^ (e - 1) * (2 ^ 149)⁻¹ := by
  rw [pow_normal32 e he]
  ring

def ty32 (x : BitVec 32) : FPType :=
  if ex32 x = 0 then (if fr32 x = 0 then .FPType_Zero else .FPType_Denormal)
  else if ex32 x = 255 then
    (if fr32 x = 0 then .FPType_Infinity else if 2 ^ 22 ≤ fr32 x then .FPType_QNaN
     else .FPType_SNaN)
  else .FPType_Nonzero

noncomputable def val32 (x : BitVec 32) : ℝ :=
  if ex32 x = 255 then
    (if fr32 x = 0 then (if sg32 x then -(2 : ℝ) ^ (1000000 : ℤ) else (2 : ℝ) ^ (1000000 : ℤ))
     else 0)
  else (Wasm.IEEE32.scaledValue (UInt32.ofBitVec x) : ℝ) * (2 : ℝ) ^ (-149 : ℤ)

theorem fpUnpack_run32 (x : BitVec 32) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPUnpack__1 x fpcrV true).run s = .ok (ty32 x, sgBit32 x, val32 x) s' ∧
      s'.regs = R ∧ Frame s s' := by
  subst hs
  refine exists_of_run (σ := ?σ) ?run ?regs ?frame
  case run =>
    sail_simp [FPUnpack__1, FPUnpackBase, FPUnpackBase__1, h.hfi, h.hps, h.nrw, h.aa64, ite_bind',
      run_ite, ite_ok, isZero_eq, isOnes_eq, ex32_eq, fr32_eq]
    refine ok_congr ?_
    rw [show ∀ A B : BitVec 8 × BitVec 23 × BitVec 1, (if false = true then A else B) = B from
      fun _ _ => rfl, sign_join32, qbit32]
    have hx := x.isLt
    unfold ty32 sgBit32 val32
    simp only [Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude, t_sign32, t_exp32, t_frac32,
      mult_real, add_real, neg_real, to_real, real_power, denorm_val32]
    have e255 : (2 : ℕ) ^ 8 - 1 = 255 := by norm_num
    rw [e255]
    by_cases h0 : ex32 x = 0 <;> by_cases h1 : fr32 x = 0 <;> by_cases h2 : ex32 x = 255 <;>
      by_cases h3 : sg32 x <;> by_cases h4 : 2 ^ 22 ≤ fr32 x <;>
      simp [h0, h1, h2, h3, h4]
    all_goals first | exact pow_normal32 _ h0 | exact val_normal32 _ h0 _
  case regs => rfl
  case frame => exact ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 800000 in
theorem fpProcessNaNs_run32 (t1 t2 : FPType) (a b : BitVec 32)
    {R : Std.ExtDHashMap Register RegisterType} (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPProcessNaNs__1 t1 t2 a b fpcrV true).run s =
      .ok (isNaNT t1 || isNaNT t2, if isNaNT t1 || isNaNT t2 then 0x7FC00000#32 else 0#32) s' ∧
      s'.regs = (if t1 == .FPType_SNaN || t2 == .FPType_SNaN then R.insert .FPSR (ioc fpsr)
        else R) ∧
      Frame s s' := by
  subst hs
  cases t1 <;> cases t2 <;> (
    apply exists_of_run
    · sail_simp [FPProcessNaNs__1, FPProcessNaN__1, FPProcessException, h.hfi,
        h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, isNaNT, ite_self]
      try sail_simp [FPDefaultNaN__1, h.hfi, h.hps, h.nrw, h.aa64, ite_self]
      rfl
    · sail_simp [ioc]
    · exact ⟨rfl, rfl, rfl, rfl⟩)

theorem t_isNaN32 (x : BitVec 32) :
    Wasm.IEEE32.isNaN (UInt32.ofBitVec x) = isNaNT (ty32 x) := by
  simp only [Wasm.IEEE32.isNaN, t_exp32, t_frac32]
  unfold ty32
  by_cases h0 : ex32 x = 0
  · simp only [h0, ite_true]
    split <;> rfl
  · by_cases h2 : ex32 x = 255
    · by_cases h1 : fr32 x = 0
      · simp only [h0, h2, h1, ite_true, ite_false]; rfl
      · have h1' : (fr32 x != 0) = true := by simpa using h1
        have h1'' : (fr32 x == 0) = false := by simpa using h1
        by_cases h3 : 2 ^ 22 ≤ fr32 x
        · rw [ite_eq_right h0, ite_eq_left h2, ite_eq_right h1, ite_eq_left h3, h2]; simp only [h1', h1'']; rfl
        · rw [ite_eq_right h0, ite_eq_left h2, ite_eq_right h1, ite_eq_right h3, h2]; simp only [h1', h1'']; rfl
    · have : (ex32 x == 0xFF) = false := by simpa using h2
      simp only [h0, h2, this, ite_false, Bool.false_and]; rfl

theorem t_isInf32 (x : BitVec 32) :
    Wasm.IEEE32.isInfinite (UInt32.ofBitVec x) = (ty32 x == .FPType_Infinity) := by
  simp only [Wasm.IEEE32.isInfinite, t_exp32, t_frac32]
  unfold ty32
  by_cases h0 : ex32 x = 0
  · simp only [h0, ite_true]
    split <;> rfl
  · by_cases h2 : ex32 x = 255
    · by_cases h1 : fr32 x = 0
      · simp only [h0, h2, h1, ite_true, ite_false]; rfl
      · have h1'' : (fr32 x == 0) = false := by simpa using h1
        by_cases h3 : 2 ^ 22 ≤ fr32 x
        · rw [ite_eq_right h0, ite_eq_left h2, ite_eq_right h1, ite_eq_left h3, h2]; simp only [h1'']; rfl
        · rw [ite_eq_right h0, ite_eq_left h2, ite_eq_right h1, ite_eq_right h3, h2]; simp only [h1'']; rfl
    · have : (ex32 x == 0xFF) = false := by simpa using h2
      simp only [h0, h2, this, ite_false, Bool.false_and]; rfl

theorem ty32_inf (x : BitVec 32) (h : ty32 x = .FPType_Infinity) : ex32 x = 255 ∧ fr32 x = 0 := by
  unfold ty32 at h
  split_ifs at h with h0 h1 h2 h3 <;> first | exact ⟨‹_›, ‹_›⟩ | cases h

theorem ty32_fin (x : BitVec 32) (h1 : ty32 x ≠ .FPType_Infinity)
    (h2 : isNaNT (ty32 x) = false) : ex32 x ≠ 255 := by
  intro he
  unfold ty32 at h1 h2
  have : ex32 x ≠ 0 := by omega
  simp only [this, he, ite_false, ite_true] at h1 h2
  split_ifs at h1 h2 <;>
    first | contradiction | exact h1 rfl | (exfalso; omega) | exact absurd h2 (by decide)

theorem ty32_zero (x : BitVec 32) (hfin : ex32 x ≠ 255) :
    Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec x) = 0 ↔ ty32 x = .FPType_Zero := by
  simp only [Wasm.IEEE32.scaledMagnitude, t_exp32, t_frac32]
  unfold ty32
  by_cases h0 : ex32 x = 0
  · simp only [h0, beq_self_eq_true, ite_true]
    by_cases h1 : fr32 x = 0 <;> simp [h1]
  · have : (ex32 x == 0) = false := by simpa using h0
    simp only [this, ite_false, Bool.false_eq_true, h0, hfin]
    constructor
    · intro hm; have := Nat.mul_eq_zero.mp hm; simp at this
    · intro hc; cases hc

theorem inf_word32 (x : BitVec 32) (h : ty32 x = .FPType_Infinity) :
    x = if sg32 x then 0xFF800000#32 else 0x7F800000#32 := by
  obtain ⟨he, hf⟩ := ty32_inf x h
  have hx := x.isLt
  unfold ex32 at he
  unfold fr32 at hf
  apply BitVec.eq_of_toNat_eq
  unfold sg32
  split <;> simp_all <;> omega

theorem val32_fin (x : BitVec 32) (h : ex32 x ≠ 255) :
    val32 x = (Wasm.IEEE32.scaledValue (UInt32.ofBitVec x) : ℝ) * (2 : ℝ) ^ (-149 : ℤ) := by
  simp [val32, h]

theorem sv32_eq (x : BitVec 32) : Wasm.IEEE32.scaledValue (UInt32.ofBitVec x) =
    if sg32 x then -(Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec x) : ℤ)
    else (Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec x) : ℤ) := by
  simp only [Wasm.IEEE32.scaledValue, t_sign32]

theorem val32_zero (x : BitVec 32) (h : ty32 x = .FPType_Zero) : val32 x = 0 := by
  have hfin : ex32 x ≠ 255 :=
    ty32_fin x (by rw [h]; exact fun h => FPType.noConfusion h) (by rw [h]; rfl)
  rw [val32_fin x hfin, sv32_eq, (ty32_zero x hfin).mpr h]
  simp

theorem sv32_zero (x : BitVec 32) (h : ty32 x = .FPType_Zero) :
    Wasm.IEEE32.scaledValue (UInt32.ofBitVec x) = 0 := by
  have hfin : ex32 x ≠ 255 :=
    ty32_fin x (by rw [h]; exact fun h => FPType.noConfusion h) (by rw [h]; rfl)
  rw [sv32_eq, (ty32_zero x hfin).mpr h]
  simp

/-- The magnitude of a binary32 word in units of 2^-149, as Talos computes it. -/
abbrev mag32 (x : BitVec 32) : ℕ := Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec x)

theorem mag32_beq_zero (x : BitVec 32) :
    (Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec x) == 0) = (ty32 x == .FPType_Zero) := by
  by_cases hf : ex32 x = 255
  · have hm : mag32 x ≠ 0 := by
      simp only [mag32, Wasm.IEEE32.scaledMagnitude, t_exp32, t_frac32, hf]
      simp
    have ht : ty32 x ≠ .FPType_Zero := by
      unfold ty32; rw [ite_eq_right (by omega), ite_eq_left hf]; split_ifs <;> simp
    simp only [beq_eq_false_iff_ne.mpr hm]
    cases h : ty32 x <;> first | rfl | exact absurd h ht
  · by_cases hz : ty32 x = .FPType_Zero
    · rw [hz, (ty32_zero x hf).mpr hz]; rfl
    · have hm : mag32 x ≠ 0 := fun h => hz ((ty32_zero x hf).mp h)
      simp only [beq_eq_false_iff_ne.mpr hm]
      cases h : ty32 x <;> first | rfl | exact absurd h hz

/-! ## Talos's binary32 words and rounders -/

theorem toBV_encode32 (neg : Bool) (e f : ℕ) :
    (Wasm.IEEE32.encodeFinite neg e f).toBitVec =
      BitVec.ofNat 32 ((if neg then 2 ^ 31 else 0) + e * 2 ^ 23 + f) := rfl

theorem toBV_inf32 (neg : Bool) :
    (Wasm.IEEE32.infinity neg).toBitVec =
      (if neg then 0xFF800000#32 else 0x7F800000#32) := by
  cases neg <;> rfl

set_option maxRecDepth 10000 in
theorem bits_eq32 (sb : BitVec 1) (be im hi1 hi2 : ℤ) (w0 : ℕ) (h1 : hi1 = 7) (h2 : hi2 = 22)
    (h0 : w0 = 0) (hbe : 0 ≤ be) (hbe' : be < 255) (him : 2 ^ 23 ≤ im) (him' : im < 2 ^ 24) :
    BitVec.setWidth 32 (sb +++ integer_subrange be hi1 0 +++ integer_subrange im hi2 0 +++
      (Zeros (n := w0))) =
      BitVec.ofNat 32 (sb.toNat * 2 ^ 31 + be.toNat * 2 ^ 23 + (im.toNat - 2 ^ 23)) := by
  subst h1 h2 h0
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append, subrange_toNat be 7 hbe (by norm_num),
    subrange_toNat im 22 (by omega) (by norm_num), Zeros, BitVec.zero, BitVec.toNat_ofNat]
  have e8 : ((7 : ℤ) - 0 + 1).toNat = 8 := rfl
  have e23 : ((22 : ℤ) - 0 + 1).toNat = 23 := rfl
  have f8 : Int.toNat 7 - Int.toNat 0 + 1 = 8 := rfl
  have f23 : Int.toNat 22 - Int.toNat 0 + 1 = 23 := rfl
  rw [e8, e23, f8, f23]
  have hb1 : be.toNat < 2 ^ 8 := by omega
  have hi1 : 2 ^ 23 ≤ im.toNat := by omega
  have hi2 : im.toNat < 2 ^ 24 := by omega
  have hs : sb.toNat < 2 := sb.isLt
  have hm : im.toNat % 2 ^ 23 = im.toNat - 2 ^ 23 := by omega
  rw [Nat.mod_eq_of_lt hb1, hm]
  have o1 : sb.toNat <<< 8 ||| be.toNat = sb.toNat * 2 ^ 8 + be.toNat := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hb1, Nat.shiftLeft_eq]
  have o2 : (sb.toNat * 2 ^ 8 + be.toNat) <<< 23 ||| (im.toNat - 2 ^ 23) =
      (sb.toNat * 2 ^ 8 + be.toNat) * 2 ^ 23 + (im.toNat - 2 ^ 23) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  have z : ∀ x : BitVec 0, x.toNat = 0 := fun x => by have := x.isLt; simp at this; omega
  have o3 : (sb.toNat * 2 ^ 8 + be.toNat) * 2 ^ 23 = sb.toNat * 2 ^ 31 + be.toNat * 2 ^ 23 := by
    rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add]
  rw [o1, o2, Nat.shiftLeft_zero, z, Nat.or_zero, o3]

set_option maxRecDepth 10000 in
theorem bits_sub32 (sb : BitVec 1) (be im hi1 hi2 : ℤ) (w0 : ℕ) (h1 : hi1 = 7) (h2 : hi2 = 22)
    (h0 : w0 = 0) (hbe : be = 0) (him : 0 ≤ im) (him' : im < 8388608) :
    BitVec.setWidth 32 (sb +++ integer_subrange be hi1 0 +++ integer_subrange im hi2 0 +++
      (Zeros (n := w0))) = BitVec.ofNat 32 (sb.toNat * 2 ^ 31 + im.toNat) := by
  subst h1 h2 h0 hbe
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append, subrange_toNat 0 7 le_rfl (by norm_num),
    subrange_toNat im 22 him (by norm_num), Zeros, BitVec.zero, BitVec.toNat_ofNat]
  have e8 : ((7 : ℤ) - 0 + 1).toNat = 8 := rfl
  have e23 : ((22 : ℤ) - 0 + 1).toNat = 23 := rfl
  have f8 : Int.toNat 7 - Int.toNat 0 + 1 = 8 := rfl
  have f23 : Int.toNat 22 - Int.toNat 0 + 1 = 23 := rfl
  rw [e8, e23, f8, f23]
  have hi2 : im.toNat < 2 ^ 23 := by omega
  have hs : sb.toNat < 2 := sb.isLt
  have z : ∀ x : BitVec 0, x.toNat = 0 := fun x => by have := x.isLt; simp at this; omega
  rw [Nat.mod_eq_of_lt hi2]
  have o0 : Int.toNat 0 % 2 ^ 8 = 0 := rfl
  have o1 : sb.toNat <<< 8 ||| 0 = sb.toNat * 2 ^ 8 := by rw [Nat.or_zero, Nat.shiftLeft_eq]
  have o2 : (sb.toNat * 2 ^ 8) <<< 23 ||| im.toNat = sb.toNat * 2 ^ 8 * 2 ^ 23 + im.toNat := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hi2, Nat.shiftLeft_eq]
  rw [o0, o1, o2, Nat.shiftLeft_zero, z, Nat.or_zero, Nat.mul_assoc, ← Nat.pow_add]

theorem rsm_exact32 (neg : Bool) (q j : ℕ) (h1 : 2 ^ 23 ≤ q) (h2 : q < 2 ^ 24) :
    Wasm.IEEE32.roundScaledMagnitude neg (q * 2 ^ j) =
      if 255 ≤ j + 1 then Wasm.IEEE32.infinity neg
      else Wasm.IEEE32.encodeFinite neg (j + 1) (q - 2 ^ 23) := by
  unfold Wasm.IEEE32.roundScaledMagnitude
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [pow_zero, Nat.mul_one]
    rw [ite_eq_right (by omega), ite_eq_left h2, ite_eq_right (by omega)]
  · have hp : 2 ^ 24 ≤ q * 2 ^ j := by
      have : 2 ≤ 2 ^ j := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      calc 2 ^ 24 = 2 ^ 23 * 2 := by norm_num
        _ ≤ q * 2 ^ j := Nat.mul_le_mul h1 this
    have hlog : Nat.log2 (q * 2 ^ j) = 23 + j := by
      apply log2_eq
      · rw [pow_add]; exact Nat.mul_le_mul_right _ h1
      · rw [show 23 + j + 1 = 24 + j by omega, pow_add]
        exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos j)
    have hrs : Wasm.IEEE32.roundShift (q * 2 ^ j) j = q := by
      rw [roundShift_eq _ _ hj, Nat.mul_mod_left, Nat.mul_div_cancel _ (Nat.two_pow_pos j)]
      rw [ite_eq_right]
      have := Nat.two_pow_pos j
      omega
    simp only [show ¬ q * 2 ^ j < 2 ^ 23 by omega, show ¬ q * 2 ^ j < 2 ^ 24 by omega, ite_false,
      hlog, show 23 + j - 23 = j by omega, hrs]
    have hq : (q == 2 ^ 24) = false := by simp only [beq_eq_false_iff_ne]; omega
    simp only [hq, Bool.false_eq_true, ite_false]

theorem rsm_carry32 (neg : Bool) (j : ℕ) :
    Wasm.IEEE32.roundScaledMagnitude neg (2 ^ 24 * 2 ^ j) =
      if 255 ≤ j + 2 then Wasm.IEEE32.infinity neg
      else Wasm.IEEE32.encodeFinite neg (j + 2) 0 := by
  rw [show 2 ^ 24 * 2 ^ j = 2 ^ 23 * 2 ^ (j + 1) by rw [← pow_add, ← pow_add]; congr 1; omega,
    rsm_exact32 neg _ _ (le_refl _) (by norm_num)]
  simp

/-- The quotient of `P` by `Q · 2^j` has 24 bits when `log2 ⌊P/Q⌋ = j + 23`. -/
theorem q_bounds32 (P Q j : ℕ) (hk : Nat.log2 (P / Q) = j + 23) :
    2 ^ 23 ≤ P / (Q * 2 ^ j) ∧ P / (Q * 2 ^ j) < 2 ^ 24 := by
  have hI0 : P / Q ≠ 0 := by intro h0; rw [h0, Nat.log2_zero] at hk; omega
  have hL1 : 2 ^ (j + 23) ≤ P / Q := by rw [← hk]; exact Nat.log2_self_le hI0
  have hL2 : P / Q < 2 ^ (j + 23 + 1) := by rw [← hk]; exact Nat.lt_log2_self
  rw [← Nat.div_div_eq_div_mul]
  constructor
  · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
    rw [show j + 23 = 23 + j by omega, pow_add] at hL1; exact hL1
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [show j + 23 + 1 = 24 + j by omega, pow_add] at hL2; exact hL2

/-- Talos's rounding for a normal result: the quotient `q` of `P` by `Q · 2^j` rounds to nearest
even, with a carry into the exponent and an overflow to infinity. -/
theorem rq_normal32 (neg : Bool) (P Q j q r : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (hk : Nat.log2 (P / Q) = j + 23) (hq : P / (Q * 2 ^ j) = q) (hr : P % (Q * 2 ^ j) = r) :
    (Wasm.IEEE32.roundRationalMagnitude neg P Q).toBitVec =
      (if (Q * 2 ^ j < 2 * r ∨ 2 * r = Q * 2 ^ j ∧ q % 2 = 1) then
        (if q + 1 = 2 ^ 24 then
          (if 255 ≤ j + 2 then (Wasm.IEEE32.infinity neg).toBitVec
           else (Wasm.IEEE32.encodeFinite neg (j + 2) 0).toBitVec)
         else (if 255 ≤ j + 1 then (Wasm.IEEE32.infinity neg).toBitVec
           else (Wasm.IEEE32.encodeFinite neg (j + 1) (q + 1 - 2 ^ 23)).toBitVec))
       else (if 255 ≤ j + 1 then (Wasm.IEEE32.infinity neg).toBitVec
         else (Wasm.IEEE32.encodeFinite neg (j + 1) (q - 2 ^ 23)).toBitVec)) := by
  obtain ⟨hq1, hq2⟩ := q_bounds32 P Q j hk
  rw [hq] at hq1 hq2
  have hd : 0 < Q * 2 ^ j := Nat.mul_pos hQ (Nat.two_pow_pos _)
  have hrq : Wasm.IEEE32.roundQuotient P (Q * 2 ^ j) =
      if (Q * 2 ^ j < 2 * r ∨ 2 * r = Q * 2 ^ j ∧ q % 2 = 1) then q + 1 else q := by
    rw [roundQuotient_eq _ _ hd, hq, hr]
  have hP0 : (P == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  have hQ0 : (Q == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  unfold Wasm.IEEE32.roundRationalMagnitude
  simp only [hP0, hQ0, Bool.false_eq_true, ite_false, hk, show j + 23 - 23 = j by omega]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hrq0 : Wasm.IEEE32.roundQuotient P Q =
        if (Q * 2 ^ 0 < 2 * r ∨ 2 * r = Q * 2 ^ 0 ∧ q % 2 = 1) then q + 1 else q := by
      rw [← hrq, pow_zero, Nat.mul_one]
    simp only [beq_self_eq_true, ite_true]
    rw [hrq0]
    by_cases hup : (Q * 2 ^ 0 < 2 * r ∨ 2 * r = Q * 2 ^ 0 ∧ q % 2 = 1)
    · rw [ite_eq_left hup, ite_eq_left hup]
      by_cases hc : q + 1 = 2 ^ 24
      · rw [ite_eq_left hc, hc]
        have e := rsm_carry32 neg 0
        rw [pow_zero, Nat.mul_one] at e
        rw [e]
        split_ifs <;> first | rfl | (exfalso; omega)
      · rw [ite_eq_right hc]
        have e := rsm_exact32 neg (q + 1) 0 (by omega) (by omega)
        rw [pow_zero, Nat.mul_one] at e
        rw [e]
        split_ifs <;> first | rfl | (exfalso; omega)
    · rw [ite_eq_right hup, ite_eq_right hup]
      have e := rsm_exact32 neg q 0 hq1 hq2
      rw [pow_zero, Nat.mul_one] at e
      rw [e]
      split_ifs <;> first | rfl | (exfalso; omega)
  · have hj' : (j == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
    simp only [hj', Bool.false_eq_true, ite_false]
    rw [hrq]
    by_cases hup : (Q * 2 ^ j < 2 * r ∨ 2 * r = Q * 2 ^ j ∧ q % 2 = 1)
    · rw [ite_eq_left hup, ite_eq_left hup]
      by_cases hc : q + 1 = 2 ^ 24
      · have hc' : (q + 1 == 2 ^ 24) = true := by simp only [beq_iff_eq]; exact hc
        rw [ite_eq_left hc]
        simp only [hc', ite_true]
        split_ifs <;> first | rfl | (exfalso; omega)
      · have hc' : (q + 1 == 2 ^ 24) = false := by simp only [beq_eq_false_iff_ne]; exact hc
        rw [ite_eq_right hc]
        simp only [hc', Bool.false_eq_true, ite_false]
        split_ifs <;> first | rfl | (exfalso; omega)
    · rw [ite_eq_right hup, ite_eq_right hup]
      have hc' : (q == 2 ^ 24) = false := by simp only [beq_eq_false_iff_ne]; omega
      simp only [hc', Bool.false_eq_true, ite_false]
      split_ifs <;> first | rfl | (exfalso; omega)

/-- Talos's rounding for a subnormal result: the quotient `q` of `P` by `Q` rounds to nearest
even, and a carry gives the smallest normal number. -/
theorem rq_sub32 (neg : Bool) (P Q q r : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hL : P / Q < 2 ^ 23)
    (hq : P / Q = q) (hr : P % Q = r) :
    (Wasm.IEEE32.roundRationalMagnitude neg P Q).toBitVec =
      if (Q < 2 * r ∨ 2 * r = Q ∧ q % 2 = 1) then
        (if q + 1 = 2 ^ 23 then (Wasm.IEEE32.encodeFinite neg 1 0).toBitVec
         else (Wasm.IEEE32.encodeFinite neg 0 (q + 1)).toBitVec)
      else (Wasm.IEEE32.encodeFinite neg 0 q).toBitVec := by
  have hlog : Nat.log2 (P / Q) - 23 = 0 := by
    rcases Nat.eq_zero_or_pos (P / Q) with h0 | h0
    · rw [h0, Nat.log2_zero]
    · have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp h0)).mpr hL
      omega
  have hq2 : q < 2 ^ 23 := hq ▸ hL
  unfold Wasm.IEEE32.roundRationalMagnitude
  have hP0 : (P == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  have hQ0 : (Q == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  simp only [hP0, hQ0, Bool.false_eq_true, ite_false, hlog, beq_self_eq_true, ite_true]
  rw [roundQuotient_eq _ _ hQ, hq, hr]
  unfold Wasm.IEEE32.roundScaledMagnitude
  by_cases hup : (Q < 2 * r ∨ 2 * r = Q ∧ q % 2 = 1)
  · rw [ite_eq_left hup, ite_eq_left hup]
    by_cases hc : q + 1 = 2 ^ 23
    · rw [ite_eq_left hc, hc, ite_eq_right (by norm_num), ite_eq_left (by norm_num)]
      simp
    · rw [ite_eq_right hc, ite_eq_left (by omega)]
  · rw [ite_eq_right hup, ite_eq_right hup, ite_eq_left hq2]

/-- The bits of FPSR that FPRoundBase__1 sets for the magnitude `P / Q` in units of 2^-149, at
32 bits under FPCR 0x02000000: OFC and IXC on overflow, IXC on an inexact result, and UFC with IXC
on an inexact subnormal result. -/
def maskQ32 (P Q : ℕ) : BitVec 64 :=
  let j := Nat.log2 (P / Q) - 23
  let q := P / (Q * 2 ^ j)
  let r := P % (Q * 2 ^ j)
  if 2 ^ 23 ≤ P / Q then
    (if 255 ≤ (if (Q * 2 ^ j < 2 * r ∨ 2 * r = Q * 2 ^ j ∧ q % 2 = 1) ∧ q + 1 = 2 ^ 24
        then j + 2 else j + 1) then 0x14#64
     else if r = 0 then 0#64 else 0x10#64)
  else if r = 0 then 0#64 else 0x18#64

theorem roundQuotient_one (n : ℕ) : Wasm.IEEE32.roundQuotient n 1 = n := by
  simp [Wasm.IEEE32.roundQuotient, Nat.mod_one]

theorem roundQuotient_pow (n k : ℕ) (hk : 1 ≤ k) :
    Wasm.IEEE32.roundQuotient n (2 ^ k) = Wasm.IEEE32.roundShift n k := by
  rw [roundQuotient_eq _ _ (Nat.two_pow_pos k), roundShift_eq _ _ hk]

/-- Talos's rounder of a sum or an integer is its rational rounder with the denominator 1. -/
theorem rsm_eq_rrm32 (neg : Bool) (N : ℕ) (hN : 0 < N) :
    Wasm.IEEE32.roundScaledMagnitude neg N = Wasm.IEEE32.roundRationalMagnitude neg N 1 := by
  have hN0 : (N == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  have h10 : ((1 : ℕ) == 0) = false := rfl
  unfold Wasm.IEEE32.roundRationalMagnitude
  simp only [hN0, h10, Nat.div_one, Nat.one_mul, Bool.false_eq_true, ite_false]
  by_cases h24 : N < 2 ^ 24
  · have hs : Nat.log2 N - 23 = 0 := by
      have := (Nat.log2_lt (by omega)).mpr h24; omega
    rw [hs, roundQuotient_one]
    simp
  · have hs : 1 ≤ Nat.log2 N - 23 := by
      have := (Nat.le_log2 (by omega)).mpr (not_lt.mp h24); omega
    have hs' : (Nat.log2 N - 23 == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
    simp only [hs', Bool.false_eq_true, ite_false, roundQuotient_pow _ _ hs]
    unfold Wasm.IEEE32.roundScaledMagnitude
    rw [ite_eq_right (by omega), ite_eq_right h24]

theorem log2_div_pow (N X : ℕ) (h : 2 ^ X ≤ N) : Nat.log2 (N / 2 ^ X) = Nat.log2 N - X := by
  have hN : N ≠ 0 := by have := Nat.two_pow_pos X; omega
  have hX : X ≤ Nat.log2 N := (Nat.le_log2 hN).mpr h
  apply log2_eq
  · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← pow_add,
      show Nat.log2 N - X + X = Nat.log2 N by omega]
    exact Nat.log2_self_le hN
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
      show Nat.log2 N - X + 1 + X = Nat.log2 N + 1 by omega]
    exact Nat.lt_log2_self

/-- Talos's rounder of a product is its rational rounder with the denominator `2^X`. -/
theorem rdm_eq_rrm32 (neg : Bool) (N X : ℕ) :
    Wasm.IEEE32.roundDyadicMagnitude neg N X =
      Wasm.IEEE32.roundRationalMagnitude neg N (2 ^ X) := by
  unfold Wasm.IEEE32.roundDyadicMagnitude Wasm.IEEE32.roundRationalMagnitude
  by_cases hN : N = 0
  · subst hN; simp
  have hN0 : (N == 0) = false := by simp only [beq_eq_false_iff_ne]; exact hN
  have hX0 : (2 ^ X == 0) = false := by
    simp only [beq_eq_false_iff_ne]; exact (Nat.two_pow_pos X).ne'
  have hsh : Nat.log2 (N / 2 ^ X) - 23 = Nat.log2 N - (X + 23) := by
    by_cases hle : 2 ^ X ≤ N
    · rw [log2_div_pow N X hle]; omega
    · rw [Nat.div_eq_of_lt (by omega), Nat.log2_zero]
      have := (Nat.log2_lt hN).mpr (show N < 2 ^ X by omega)
      omega
  simp only [hN0, hX0, Bool.false_eq_true, ite_false, hsh]
  by_cases hs : Nat.log2 N - (X + 23) = 0
  · simp only [hs, beq_self_eq_true, ite_true]
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · simp [roundQuotient_one]
    · have hX' : (X == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
      simp only [hX', Bool.false_eq_true, ite_false, roundQuotient_pow _ _ hX]
  · have hs' : (Nat.log2 N - (X + 23) == 0) = false := by
      simp only [beq_eq_false_iff_ne]; exact hs
    simp only [hs', Bool.false_eq_true, ite_false, ← pow_add,
      roundQuotient_pow _ _ (show 1 ≤ X + (Nat.log2 N - (X + 23)) by omega)]

/-! ## FPRoundBase__1 at 32 bits -/

/-- The exponent of `x · 2^-149` with `x < 2^23` lies below the minimum normal exponent. -/
theorem exp_subR32 (x : ℝ) (S e : ℤ) (hS : S = 149) (hx : x < 2 ^ 23)
    (h1 : 1 ≤ x * (2 : ℝ) ^ (-S) * 2 ^ (-e)) : e < -126 := by
  have ht : x * (2 : ℝ) ^ (-S) * 2 ^ (-e) = x * 2 ^ (-S - e) := by
    rw [mul_assoc, ← zpow_add₀ two_ne_zero]; ring_nf
  rw [ht] at h1
  have hpos : (0 : ℝ) < 2 ^ (-S - e) := zpow_pos (by norm_num) _
  have hx' : x < (2 : ℝ) ^ (23 : ℤ) := by rw [zpow_ofNat]; exact hx
  have a1 : (2 : ℝ) ^ (0 : ℤ) < 2 ^ ((23 : ℤ) + (-S - e)) := by
    rw [zpow_add₀ two_ne_zero, zpow_zero]
    calc (1 : ℝ) ≤ x * 2 ^ (-S - e) := h1
      _ < 2 ^ (23 : ℤ) * 2 ^ (-S - e) := mul_lt_mul_of_pos_right hx' hpos
  rw [zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)] at a1
  omega

theorem man_normalQ32 (P Q j : ℕ) (S e : ℤ) (hS : S = 149) (hE : e = (j : ℤ) - 126) :
    mult_real ((P : ℝ) / (Q : ℝ) * 2 ^ (-S) * 2 ^ (-e)) (real_power 2 23) =
      (P : ℝ) / ((Q * 2 ^ j : ℕ) : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp only [mult_real, real_power]
  rw [mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero,
    show -S + (-e + 23) = -(j : ℤ) by omega, zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_div]

theorem man_subQ32 (x : ℝ) (S e : ℤ) (hS : S = 149) :
    mult_real (div_real (x * 2 ^ (-S) * 2 ^ (-e)) (real_power 2 (-126 - e)))
      (real_power 2 23) = x := by
  simp only [mult_real, div_real, real_power]
  rw [div_eq_mul_inv, ← zpow_neg, mul_assoc, mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero,
    ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero,
    show -S + (-e + (-(-126 - e) + 23)) = 0 by omega, zpow_zero, mul_one]

set_option maxHeartbeats 1300000 in
theorem round_normalQ32 (neg : Bool) (P Q j : ℕ) (S : ℤ) (hS : S = 149) (hP : 0 < P)
    (hQ : 0 < Q) (hL : Nat.log2 (P / Q) = j + 23) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (qop neg P Q S) fpcrV .FPRounding_TIEEVEN true 32).run s =
      .ok (Wasm.IEEE32.roundRationalMagnitude neg P Q).toBitVec s' ∧
        s'.regs = R.insert .FPSR (fpsr ||| maskQ32 P Q) ∧ Frame s s' := by
  subst hs
  have hM : (0 : ℝ) < (P : ℝ) / (Q : ℝ) * (2 : ℝ) ^ (-S) :=
    mul_pos (div_pos (by exact_mod_cast hP) (by exact_mod_cast hQ)) (zpow_pos (by norm_num) _)
  obtain ⟨e, he, h1, h2⟩ := loops_eq' _ hM
  have hI0 : P / Q ≠ 0 := by intro h0; rw [h0, Nat.log2_zero] at hL; omega
  obtain ⟨hx1, hx2⟩ := div_bounds P Q (j + 23) hQ (by rw [← hL]; exact Nat.log2_self_le hI0)
    (by rw [← hL]; exact Nat.lt_log2_self)
  have hE0 := exp_eqR _ (j + 23) S e hx1 hx2 h1 h2
  have hE : e = (j : ℤ) - 126 := by omega
  obtain ⟨hlt, hne, hneg⟩ := qop_facts neg P Q S hP hQ
  have hman := man_normalQ32 P Q j S e hS hE
  have hb : max (e - -126 + 1) 0 = (j : ℤ) + 1 := by omega
  have hb0 : ((j : ℤ) + 1 == 0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  have hd : 0 < Q * 2 ^ j := Nat.mul_pos hQ (Nat.two_pow_pos _)
  have hmask : maskQ32 P Q = (let q := P / (Q * 2 ^ j); let r := P % (Q * 2 ^ j)
      if 255 ≤ (if (Q * 2 ^ j < 2 * r ∨ 2 * r = Q * 2 ^ j ∧ q % 2 = 1) ∧ q + 1 = 2 ^ 24
        then j + 2 else j + 1) then 0x14#64 else if r = 0 then 0#64 else 0x10#64) := by
    have h23 : 2 ^ 23 ≤ P / Q := (Nat.le_log2 hI0).mp (by omega)
    simp only [maskQ32, hL, h23, ite_true, show j + 23 - 23 = j by omega]
  rw [hmask, rq_normal32 neg P Q j _ _ hP hQ hL rfl rfl]
  obtain ⟨hq1, hq2⟩ := q_bounds32 P Q j hL
  have hr : P % (Q * 2 ^ j) < Q * 2 ^ j := Nat.mod_lt _ hd
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, qop] at hlt hne ⊢
  all_goals (
    sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self,
      whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt, hneg]
    rw [he]
    sail_simp [↓join1_beq, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self, hne, bne, hlt, hb,
      hb0, hman, floor_div_nat, err_div _ _ hd, gt_half _ _ hd, eq_half _ _ hd,
      beq_zero_div _ _ hd, int_access]
    generalize hq : P / (Q * 2 ^ j) = q at *
    generalize hrr : P % (Q * 2 ^ j) = r at *
    generalize hdd : Q * 2 ^ j = d at *
    clear he h1 h2 hlt hne hb hb0 hmask hE hE0 hman hx1 hx2
    simp only [ipow, Int.reduceToNat, Int.reducePow, Int.reduceSub, Int.reduceAdd, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ge_iff_le]
    have hfd : fdiv_int ((q : ℤ) + 1) 2 = ((q : ℤ) + 1) / 2 := fdiv_two _ (by omega)
    have c2 : ((q : ℤ) + 1 = 8388608) = False := by simp; omega
    have o1 : (255 ≤ (j : ℤ) + 1 + 1) = (255 ≤ j + 2) := by
      apply propext; constructor <;> intro <;> omega
    have o2 : (255 ≤ (j : ℤ) + 1) = (255 ≤ j + 1) := by
      apply propext; constructor <;> intro <;> omega
    simp only [c2, ↓reduceIte]
    by_cases hup : (d < 2 * r ∨ 2 * r = d ∧ q % 2 = 1) <;>
    by_cases hc : q + 1 = 2 ^ 24 <;> by_cases hv1 : 255 ≤ j + 1 <;> by_cases hv2 : 255 ≤ j + 2 <;>
    by_cases hr0 : r = 0
    all_goals first | (exfalso; omega) | skip
    all_goals (
      have hcI : ((q : ℤ) + 1 = 16777216) = (q + 1 = 2 ^ 24) := by
        apply propext; constructor <;> intro <;> omega
      have e1 := by first | exact eq_false hup | exact eq_true hup
      have e2 := by first | exact eq_false hc | exact eq_true hc
      have e3 := by first | exact eq_false hv1 | exact eq_true hv1
      have e4 := by first | exact eq_false hv2 | exact eq_true hv2
      have e5 := by first | exact eq_false hr0 | exact eq_true hr0
      simp only [hcI, e1, e2, e3, e4, e5, and_true, and_false, ↓reduceIte]
      try simp only [o1, o2, e3, e4, ↓reduceIte]
      apply exists_of_run'
      · sail_simp [FPInfinity, FPProcessException, h.hfi, h.hps, h.nrw, h.aa64, h.fa,
          h.hfpsr, ite_self, toBV_inf32, toBV_encode32, one_beq_zero, beq_zero_div _ _ hd,
          cast_eq, e5]
        refine ok_congr ?_
        first
        | decide
        | (rw [bits_eq32]
           · apply congrArg (BitVec.ofNat 32)
             simp only [BitVec.toNat_ofNat, Nat.zero_mod, zero_mul, zero_add, hfd, Nat.reducePow]
             omega
           all_goals first | decide | omega)
      · simp only [setReg_regs, bump_regs, faS_regs, insert_insert,
          upd_or _ _ (by norm_num : 2 < 64), upd_or _ _ (by norm_num : 4 < 64), (or_masks _).1,
          (or_masks _).2.1, BitVec.or_zero] <;>
          first | rfl | exact (insert_self _ _ _ h.hfpsr).symm
      · exact ⟨rfl, rfl, rfl, rfl⟩))

set_option maxHeartbeats 400000 in
theorem round_subQ32 (neg : Bool) (P Q : ℕ) (S : ℤ) (hS : S = 149) (hP : 0 < P) (hQ : 0 < Q)
    (hL : P / Q < 2 ^ 23) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (qop neg P Q S) fpcrV .FPRounding_TIEEVEN true 32).run s =
      .ok (Wasm.IEEE32.roundRationalMagnitude neg P Q).toBitVec s' ∧
        s'.regs = R.insert .FPSR (fpsr ||| maskQ32 P Q) ∧ Frame s s' := by
  subst hs
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hM : (0 : ℝ) < (P : ℝ) / (Q : ℝ) * (2 : ℝ) ^ (-S) :=
    mul_pos (div_pos (by exact_mod_cast hP) hQ') (zpow_pos (by norm_num) _)
  obtain ⟨e, he, h1, h2⟩ := loops_eq' _ hM
  have hx : (P : ℝ) / (Q : ℝ) < 2 ^ 23 := by
    rw [div_lt_iff₀ hQ']
    have : P < 2 ^ 23 * Q := (Nat.div_lt_iff_lt_mul hQ).mp hL
    exact_mod_cast this
  have hE := exp_subR32 _ S e hS hx h1
  obtain ⟨hlt, hne, hneg⟩ := qop_facts neg P Q S hP hQ
  have hb : max (e - -126 + 1) 0 = 0 := by omega
  have hmask : maskQ32 P Q = (if P % Q = 0 then 0#64 else 0x18#64) := by
    have hlog : Nat.log2 (P / Q) - 23 = 0 := by
      rcases Nat.eq_zero_or_pos (P / Q) with h0 | h0
      · rw [h0, Nat.log2_zero]
      · have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp h0)).mpr hL
        omega
    simp only [maskQ32, show ¬ 2 ^ 23 ≤ P / Q by omega, ite_false, hlog, pow_zero, Nat.mul_one]
  rw [hmask, rq_sub32 neg P Q _ _ hP hQ hL rfl rfl]
  have hr : P % Q < Q := Nat.mod_lt _ hQ
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, qop] at hlt hne ⊢
  all_goals (
    sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self,
      whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt, hneg]
    rw [he]
    sail_simp [↓join1_beq, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self, hne, bne, hlt, hb,
      man_subQ32 _ S e hS, floor_div_nat, err_div _ _ hQ, gt_half _ _ hQ, eq_half _ _ hQ,
      beq_zero_div _ _ hQ, int_access]
    generalize hq : P / Q = q at *
    generalize hrr : P % Q = r at *
    clear he h1 h2 hlt hne hb hmask hE hx
    simp only [ipow, Int.reduceToNat, Int.reducePow, Int.reduceSub, Int.reduceAdd, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ge_iff_le]
    have c1 : ((q : ℤ) + 1 = 16777216) = False := by simp; omega
    have c2 : ((q : ℤ) + 1 = 8388608) = (q + 1 = 2 ^ 23) := by
      apply propext; constructor <;> intro <;> omega
    simp only [c1, c2, ↓reduceIte]
    by_cases hup : (Q < 2 * r ∨ 2 * r = Q ∧ q % 2 = 1) <;>
    by_cases hc : q + 1 = 2 ^ 23 <;> by_cases hr0 : r = 0
    all_goals first | (exfalso; omega) | skip
    all_goals (
      have e1 := by first | exact eq_false hup | exact eq_true hup
      have e2 := by first | exact eq_false hc | exact eq_true hc
      have e5 := by first | exact eq_false hr0 | exact eq_true hr0
      simp only [e1, e2, e5, ↓reduceIte, decide_true, decide_false, Bool.not_true, Bool.not_false]
      apply exists_of_run'
      · sail_simp [FPZero, FPProcessException, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr,
          ite_self, toBV_encode32, one_beq_zero, beq_zero_div _ _ hQ, cast_eq, e5]
        refine ok_congr ?_
        first
        | decide
        | (rw [bits_sub32]
           · apply congrArg (BitVec.ofNat 32)
             simp only [BitVec.toNat_ofNat, Nat.zero_mod, zero_mul, zero_add, Nat.reducePow]
             omega
           all_goals first | decide | omega)
        | (rw [bits_eq32]
           · apply congrArg (BitVec.ofNat 32)
             simp only [BitVec.toNat_ofNat, Nat.zero_mod, zero_mul, zero_add, Nat.reducePow]
             have hq1 : ((q : ℤ) + 1).toNat = 8388608 := by
               have : ((q : ℤ) + 1) = ((q + 1 : ℕ) : ℤ) := by push_cast; rfl
               rw [this, Int.toNat_natCast, hc]; rfl
             rw [hq1]
             rfl
           all_goals first | decide | (clear * - hc; omega))
      · simp only [setReg_regs, bump_regs, faS_regs, insert_insert,
          upd_or _ _ (by norm_num : 3 < 64), upd_or _ _ (by norm_num : 4 < 64), (or_masks _).2.2.2,
          BitVec.or_zero] <;>
          first | rfl | exact (insert_self _ _ _ h.hfpsr).symm
      · exact ⟨rfl, rfl, rfl, rfl⟩))

/-- FPRound__2 at 32 bits under FPCR 0x02000000, rounding to nearest even, on `±(P/Q) · 2^-149`
returns Talos's `IEEE32.roundRationalMagnitude` and sets the FPSR bits of `maskQ32 P Q`. -/
theorem fpRound32_q (neg : Bool) (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    {R : Std.ExtDHashMap Register RegisterType} (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (qop neg P Q 149) fpcrV .FPRounding_TIEEVEN true 32).run s =
      .ok (Wasm.IEEE32.roundRationalMagnitude neg P Q).toBitVec s' ∧
        s'.regs = R.insert .FPSR (fpsr ||| maskQ32 P Q) ∧ Frame s s' := by
  by_cases hL : 2 ^ 23 ≤ P / Q
  · have hI0 : P / Q ≠ 0 := by omega
    have h23 : 23 ≤ Nat.log2 (P / Q) := (Nat.le_log2 hI0).mpr hL
    exact round_normalQ32 neg P Q (Nat.log2 (P / Q) - 23) 149 rfl hP hQ (by omega) h hs
  · exact round_subQ32 neg P Q 149 rfl hP hQ (by omega) h hs

end F7
