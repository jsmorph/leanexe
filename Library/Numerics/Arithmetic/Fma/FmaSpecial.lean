import Library.Numerics.Arithmetic.Fma.FmaGeneral

/-!
The special cases of `Fma.fmaBits` and facts about the nearest-even reference.  `fmaBits` returns
the first NaN operand with its quiet bit set (`fmaBits_nan_a`, `fmaBits_nan_b`, `fmaBits_nan_c`),
the default NaN or a signed infinity for an infinite factor (`fmaBits_inf`), `c` for an infinite
`c` and finite factors (`fmaBits_inf_c`), and `c` or a signed zero for a zero product
(`fmaBits_zero_product`).  The reference of the value of a nonzero finite word is the word
(`reference_self`), and no reference is a NaN (`reference_not_nan`).
-/

namespace Library.Numerics.Arithmetic.Fma.FmaSpecial
open Verified.Examples FmaWords FmaDecode FmaParts FmaCombine FmaGeneral FmaGrid FmaRound
open FmaNearestEven CodeLib.IEEE64 LeanExe.ProofKit

theorem quiet_nan (x : UInt64) (hx : Wasm.IEEE64.isNaN x = true) :
    Wasm.IEEE64.isNaN (x ||| 0x8000000000000) = true := by
  unfold Wasm.IEEE64.isNaN Wasm.IEEE64.exponent Wasm.IEEE64.fraction at *
  rw [UInt64.toNat_or]
  have hq : (0x8000000000000 : UInt64).toNat = 2 ^ 51 := rfl
  have he : (x.toNat ||| 2 ^ 51) / 2 ^ 52 = x.toNat / 2 ^ 52 := by
    rw [Nat.or_div_two_pow, show (2 : ℕ) ^ 51 / 2 ^ 52 = 0 by norm_num, Nat.or_zero]
  have hf : (x.toNat ||| 2 ^ 51) % 2 ^ 52 = x.toNat % 2 ^ 52 ||| 2 ^ 51 := by
    rw [Nat.or_mod_two_pow, show (2 : ℕ) ^ 51 % 2 ^ 52 = 2 ^ 51 by norm_num]
  rw [hq, he, hf]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hx ⊢
  refine ⟨hx.1, ?_⟩
  rw [Nat.or_eq_zero_iff]
  intro h
  exact absurd h.2 (by positivity)

theorem inf_test (x : UInt64) (hx : Wasm.IEEE64.isNaN x = false) :
    ((x >>> 52) &&& 0x7FF == 0x7FF) = Wasm.IEEE64.isInfinite x := by
  rw [exponent_beq]
  have h7 : (0x7FF : UInt64).toNat = 2047 := rfl
  rw [h7]
  unfold Wasm.IEEE64.isInfinite
  unfold Wasm.IEEE64.isNaN at hx
  by_cases he : Wasm.IEEE64.exponent x = 2047
  · have hf : Wasm.IEEE64.fraction x = 0 := by simpa [he] using hx
    simp [he, hf]
  · simp [he]

theorem zero_beq (x : UInt64) : (x <<< 1 == 0) = (Wasm.IEEE64.scaledMagnitude x == 0) := by
  rw [zero_bits, Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]

theorem shr63_eq (x : UInt64) : x >>> 63 = if Wasm.IEEE64.sign x then 1 else 0 := by
  apply UInt64.toNat_inj.mp
  rw [sign_bit]
  split_ifs <;> rfl

theorem xor63_eq (a b : UInt64) :
    (a ^^^ b) >>> 63 = if Wasm.IEEE64.sign a != Wasm.IEEE64.sign b then 1 else 0 := by
  apply UInt64.toNat_inj.mp
  rw [sign_xor_bit]
  split_ifs <;> rfl

theorem finite_of (x : UInt64) (hn : Wasm.IEEE64.isNaN x = false)
    (hi : Wasm.IEEE64.isInfinite x = false) : Finite x := by
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite
  unfold Wasm.IEEE64.isNaN at hn
  unfold Wasm.IEEE64.isInfinite at hi
  by_cases he : Wasm.IEEE64.exponent x = 0x7FF
  · by_cases hf : Wasm.IEEE64.fraction x = 0
    · simp [he, hf] at hi
    · simp [he, hf] at hn
  · simpa using he

theorem value_ne_zero (x : UInt64) (hx : Wasm.IEEE64.scaledMagnitude x ≠ 0) : value x ≠ 0 := by
  rw [value_units]
  have := msig_pos x hx
  apply div_ne_zero _ (by positivity)
  apply mul_ne_zero (by split_ifs <;> norm_num)
  positivity

/-- The fields of a finite word give back its magnitude bits. -/
theorem word_split (c : UInt64) (hc : Finite c) :
    (mexp c - 1) * 2 ^ 52 + msig c = c.toNat % 2 ^ 63 ∧
      (mexp c - 1) * 2 ^ 52 + msig c < 0x7FF0000000000000 := by
  have hf : Wasm.IEEE64.exponent c ≠ 0x7FF := by
    simpa [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite] using hc
  have hx := c.toNat_lt
  unfold mexp msig at *
  unfold Wasm.IEEE64.exponent Wasm.IEEE64.fraction at *
  simp only [Nat.reducePow] at *
  split_ifs <;> omega

theorem pack_self (c : UInt64) (hc : Finite c) : packWord (c >>> 63) (mexp c) (msig c) = c := by
  obtain ⟨h1, h2⟩ := word_split c hc
  have he := mexp_le c hc
  unfold packWord
  rw [ite_eq_right (by omega), ite_eq_right (by omega), h1]
  apply UInt64.toNat_inj.mp
  have hlt : c.toNat % 2 ^ 63 < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by positivity)) (by norm_num)
  have hx := c.toNat_lt
  have hs : (c >>> 63).toNat = c.toNat / 2 ^ 63 := by rw [shr_toNat]; rfl
  have hq : c.toNat / 2 ^ 63 ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred (by positivity)]
    simp only [Nat.reducePow] at *
    omega
  have hshl : ((c >>> 63) <<< 63).toNat = 2 ^ 63 * (c.toNat / 2 ^ 63) := by
    rw [shl_toNat, hs]
    have : (63 : UInt64).toNat % 64 = 63 := rfl
    rw [this, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by
      rcases (show c.toNat / 2 ^ 63 = 0 ∨ c.toNat / 2 ^ 63 = 1 by omega) with h | h <;>
        rw [h] <;> norm_num)
  rw [UInt64.toNat_or, hshl, UInt64.toNat_ofNat_of_lt' hlt,
    ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by positivity)), Nat.div_add_mod]

/-- The nearest-even reference of the value of a nonzero finite word is the word. -/
theorem reference_self (c : UInt64) (hc : Finite c) (hc0 : Wasm.IEEE64.scaledMagnitude c ≠ 0) :
    F64SignedRounding.roundNearestEven (value c) = c := by
  have hpos := msig_pos c hc0
  have hsp : msig c * 2 ^ (mexp c + 1325) = msig c * spacing (mexp c) := by
    unfold spacing; rfl
  have hlo : mexp c = 1 ∨ 2 ^ 52 * spacing (mexp c) ≤ msig c * 2 ^ (mexp c + 1325) := by
    by_cases h0 : Wasm.IEEE64.exponent c = 0
    · left; unfold mexp; rw [ite_eq_left h0]
    · right
      rw [hsp]
      apply Nat.mul_le_mul_right
      unfold msig
      rw [ite_eq_right h0]
      exact Nat.le_add_right _ _
  have hR := roundsTo_exact (msig c * 2 ^ (mexp c + 1325)) (mexp c) (msig c) (mexp_pos c) hsp
    (by rw [hsp]; exact Nat.mul_lt_mul_of_pos_right (msig_lt c) (spacing_pos _)) hlo
  have hY : 0 < msig c * 2 ^ (mexp c + 1325) := by positivity
  have hval : value c = (if c >>> 63 = 1 then -((msig c * 2 ^ (mexp c + 1325) : ℕ) : ℝ)
      else ((msig c * 2 ^ (mexp c + 1325) : ℕ) : ℝ)) / 2 ^ 2400 := by
    rw [value_units, shr63_eq]
    cases Wasm.IEEE64.sign c
    · rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
        ite_eq_right (by decide), one_mul]
    · rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, neg_one_mul, neg_div]
  rw [hval, signed_reference _ _ _ (c >>> 63) (sign_cases _ (sign_bit_le c)) hY hR, pack_self c hc]

theorem nan_negate (w : UInt64) : Wasm.IEEE64.isNaN (Wasm.IEEE64.negate w) = Wasm.IEEE64.isNaN w := by
  unfold Wasm.IEEE64.isNaN Wasm.IEEE64.negate
  rw [exponent_encodeFinite _ _ _ (by simpa using exponent_lt w) (fraction_lt w),
    fraction_encodeFinite _ _ _ (by simpa using exponent_lt w) (fraction_lt w)]

theorem positive_not_nan (y : ℝ) :
    Wasm.IEEE64.isNaN (F64PositiveRounding.roundNearestEven y) = false := by
  have h := F64SignedRounding.positive_reference_le y
  unfold Wasm.IEEE64.isNaN Wasm.IEEE64.exponent Wasm.IEEE64.fraction
  generalize (F64PositiveRounding.roundNearestEven y).toNat = n at h ⊢
  rw [Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]
  simp only [Nat.reducePow] at *
  omega

/-- No nearest-even reference is a NaN. -/
theorem reference_not_nan (y : ℝ) :
    Wasm.IEEE64.isNaN (F64SignedRounding.roundNearestEven y) = false := by
  unfold F64SignedRounding.roundNearestEven
  split_ifs
  · exact positive_not_nan y
  · rw [nan_negate]; exact positive_not_nan (-y)

theorem fmaBits_nan_a (a b c : UInt64) (h : Wasm.IEEE64.isNaN a = true) :
    Fma.fmaBits a b c = a ||| 0x8000000000000 := by
  rw [fmaBits_eq, nan_bits a, ite_eq_left h]

theorem fmaBits_nan_b (a b c : UInt64) (ha : Wasm.IEEE64.isNaN a = false)
    (h : Wasm.IEEE64.isNaN b = true) : Fma.fmaBits a b c = b ||| 0x8000000000000 := by
  rw [fmaBits_eq, nan_bits a, nan_bits b, ha, ite_eq_right Bool.false_ne_true, ite_eq_left h]

theorem fmaBits_nan_c (a b c : UInt64) (ha : Wasm.IEEE64.isNaN a = false)
    (hb : Wasm.IEEE64.isNaN b = false) (h : Wasm.IEEE64.isNaN c = true) :
    Fma.fmaBits a b c = c ||| 0x8000000000000 := by
  rw [fmaBits_eq, nan_bits a, nan_bits b, nan_bits c, ha, hb, ite_eq_right Bool.false_ne_true,
    ite_eq_right Bool.false_ne_true, ite_eq_left h]

theorem fmaBits_inf (a b c : UInt64) (ha : Wasm.IEEE64.isNaN a = false)
    (hb : Wasm.IEEE64.isNaN b = false) (hc : Wasm.IEEE64.isNaN c = false)
    (h : (Wasm.IEEE64.isInfinite a || Wasm.IEEE64.isInfinite b) = true) :
    Fma.fmaBits a b c =
      if Wasm.IEEE64.scaledMagnitude a == 0 || Wasm.IEEE64.scaledMagnitude b == 0 ||
          (Wasm.IEEE64.isInfinite c && c >>> 63 != (a ^^^ b) >>> 63) then (0x7FF8000000000000 : UInt64)
      else (((a ^^^ b) >>> 63) <<< 63) ||| 0x7FF0000000000000 := by
  rw [fmaBits_eq, nan_bits a, nan_bits b, nan_bits c, ha, hb, hc,
    ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
    ite_eq_right Bool.false_ne_true, inf_test a ha, inf_test b hb, ite_eq_left h, zero_beq a,
    zero_beq b, inf_test c hc]

theorem fmaBits_inf_c (a b c : UInt64) (ha : Wasm.IEEE64.isNaN a = false)
    (hb : Wasm.IEEE64.isNaN b = false) (hc : Wasm.IEEE64.isNaN c = false)
    (h : (Wasm.IEEE64.isInfinite a || Wasm.IEEE64.isInfinite b) = false)
    (hic : Wasm.IEEE64.isInfinite c = true) : Fma.fmaBits a b c = c := by
  rw [fmaBits_eq, nan_bits a, nan_bits b, nan_bits c, ha, hb, hc,
    ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
    ite_eq_right Bool.false_ne_true, inf_test a ha, inf_test b hb, h,
    ite_eq_right Bool.false_ne_true, inf_test c hc, ite_eq_left hic]

theorem fmaBits_zero_product (a b c : UInt64) (ha : Wasm.IEEE64.isNaN a = false)
    (hb : Wasm.IEEE64.isNaN b = false) (hc : Wasm.IEEE64.isNaN c = false)
    (h : (Wasm.IEEE64.isInfinite a || Wasm.IEEE64.isInfinite b) = false)
    (hic : Wasm.IEEE64.isInfinite c = false)
    (hz : (Wasm.IEEE64.scaledMagnitude a == 0 || Wasm.IEEE64.scaledMagnitude b == 0) = true) :
    Fma.fmaBits a b c = if Wasm.IEEE64.scaledMagnitude c == 0 then
      (((a ^^^ b) >>> 63) &&& (c >>> 63)) <<< 63 else c := by
  rw [fmaBits_eq, nan_bits a, nan_bits b, nan_bits c, ha, hb, hc,
    ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
    ite_eq_right Bool.false_ne_true, inf_test a ha, inf_test b hb, h,
    ite_eq_right Bool.false_ne_true, inf_test c hc, hic, ite_eq_right Bool.false_ne_true,
    zero_beq a, zero_beq b, ite_eq_left hz, zero_beq c]

#print axioms quiet_nan
#print axioms reference_self
#print axioms reference_not_nan
#print axioms fmaBits_inf
#print axioms fmaBits_zero_product

end Library.Numerics.Arithmetic.Fma.FmaSpecial
