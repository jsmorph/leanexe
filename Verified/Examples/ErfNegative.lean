import Verified.Examples.ErfPositive
import LeanExe.ProofKit.F64NegateOps

/-!
One step for `Erf.erfWith Exp.expTable x` for finite `x` with the sign bit set.  The code computes
the negation of its result at `-x`: below 0.84375 it applies the same operations to `x`, and
negating the operands of a sum or product negates the result (`F64NegateOps`), while from 0.84375
on it computes from `|x|` and negates the final sum through the sign flag.  Negating the terms of
a sum negates the rounded sum only when the exact sum is not zero, and `add_ne_zero_of_within`
excludes a zero sum from the step at `-x`: a zero sum rounds to positive zero, more than one step
from the reference of a number above `2^-1073`.  `finite_of_within_add` gives the finiteness of the
second term in the same way.  `erf` is odd, so `F64SignedRounding.within_negate` carries the step
from `-x` to `x`.
-/

namespace Verified.Examples.ErfNegative
open CodeLib.IEEE64 LeanExe.ProofKit F64Horner RealErf ErfSmallBase ErfMiddleBase ErfTailSplit
  ErfTailEval ErfEnds ErfSub ErfBits ErfPositive F64NegateOps

set_option exponentiation.threshold 4096

/-- The reference of a number in `[0, 2]` lies at or below the word of 2. -/
theorem reference_le_two (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 2) :
    F64SignedRounding.roundNearestEven y = F64NearestEven.roundNearestEven y ∧
      (F64NearestEven.roundNearestEven y).toNat ≤ 0x4000000000000000 := by
  have hyt : y < F64PositiveRounding.overflowThreshold := by
    have : (2 : ℝ) < F64PositiveRounding.overflowThreshold := by
      rw [show F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 from rfl]
      norm_num
    linarith
  refine ⟨by simp only [F64SignedRounding.roundNearestEven, hy0, ite_true,
    F64PositiveRounding.reference_finite y hyt], ?_⟩
  have hw := (F64NearestEven.roundNearestEven_spec y).1
  have hlim : F64NearestNonnegative.limit < 2 ^ 63 := by decide
  have h2 : value (0x4000000000000000 : UInt64) = 2 := by
    have : Wasm.IEEE64.scaledValue (0x4000000000000000 : UInt64) = 2 ^ 1075 := by decide +kernel
    rw [value, this]
    norm_num
  by_contra hn
  push_neg at hn
  have hlt := F64PositiveOrder.value_strict (left := (0x4000000000000000 : UInt64))
    (lt_trans hw.1 hlim) hn
  rw [h2] at hlt
  have hd := hw.2 0x4000000000000000 (by decide)
  rw [h2, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hd
  linarith

/-- A sum whose result lies within one step of a number in `[2^-1073, 2]` has a finite second
term. -/
theorem finite_of_within_add (a c : UInt64) (ha : Finite a) (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 2)
    (h : F64SignedRounding.WithinSteps 1 y (Wasm.IEEE64.add a c)) : Finite c := by
  by_contra hc
  have he : Wasm.IEEE64.exponent c = 2047 := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq, not_not] at hc
    exact hc
  by_cases hn : Wasm.IEEE64.isNaN c = true
  · have h0 : Wasm.IEEE64.add a c = Wasm.IEEE64.canonicalNaN := by
      simp [Wasm.IEEE64.add, hn]
    rw [h0] at h
    exact absurd h.1 (by decide)
  · have hf : Wasm.IEEE64.fraction c = 0 := by
      simp only [Wasm.IEEE64.isNaN, he, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
        true_and, not_not] at hn
      exact hn
    have hi : Wasm.IEEE64.isInfinite c = true := by
      simp [Wasm.IEEE64.isInfinite, he, hf]
    have h0 : Wasm.IEEE64.add a c = c := by
      simp [Wasm.IEEE64.add, not_nan_of_finite ha, hn, hi, not_infinite_of_finite ha]
    rw [h0] at h
    obtain ⟨href, hle⟩ := reference_le_two y hy0 hy
    obtain ⟨_, hpos⟩ := h
    have hlim : F64NearestNonnegative.limit < 2 ^ 63 := by decide
    rw [href, F64SignedRounding.position_of_lt (F64NearestEven.roundNearestEven y) (by omega)] at hpos
    have hct := c.toNat_lt
    have hsz : UInt64.size = 18446744073709551616 := rfl
    have hc' : c.toNat % 2 ^ 63 = 0x7FF0000000000000 := by
      simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at he hf
      omega
    have hpc : F64SignedRounding.position c = 0x7FF0000000000000 ∨
        F64SignedRounding.position c = -0x7FF0000000000000 := by
      unfold F64SignedRounding.position Wasm.IEEE64.sign
      by_cases h1 : 2 ^ 63 ≤ c.toNat
      · right
        simp only [h1, decide_true, ite_true]
        omega
      · left
        simp only [h1, decide_false, Bool.false_eq_true, ite_false]
        omega
    rcases hpc with h1 | h1 <;> rw [h1, abs_le] at hpos <;> omega

/-- A sum whose result lies within one step of a number in `[2^-1073, 2]`, with a first term with
a clear sign bit, has a nonzero exact value. -/
theorem add_ne_zero_of_within (a c : UInt64) (y : ℝ) (hy : 2 / 2 ^ 1074 ≤ y) (hy2 : y ≤ 2)
    (ha : Finite a) (hc : Finite c) (hs : Wasm.IEEE64.sign a = false)
    (h : F64SignedRounding.WithinSteps 1 y (Wasm.IEEE64.add a c)) :
    Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue c ≠ 0 := by
  intro hz
  have h0 : Wasm.IEEE64.add a c = 0 := by
    simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hc, not_infinite_of_finite ha,
      not_infinite_of_finite hc, hz, hs]
  rw [h0] at h
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  obtain ⟨href, _⟩ := reference_le_two y hy0 hy2
  have hw := (F64NearestEven.roundNearestEven_spec y).1
  have hv2 : value (UInt64.ofNat 2) = 2 / 2 ^ 1074 := by
    have : Wasm.IEEE64.scaledValue (UInt64.ofNat 2) = 2 := by decide
    rw [value, this]
    norm_num
  have hge := F64AddNearest.nearest_ge y _ 2 (by decide) hw (by rw [hv2]; exact hy)
  have hlim : F64NearestNonnegative.limit < 2 ^ 63 := by decide
  obtain ⟨_, hpos⟩ := h
  rw [href, F64SignedRounding.position_of_lt _ (lt_trans hw.1 hlim)] at hpos
  have hp0 : F64SignedRounding.position 0 = 0 := by decide
  rw [hp0, abs_le] at hpos
  omega

/-- A rounded product of a nonzero finite word is finite only when the other factor is. -/
theorem finite_of_mul_finite (a b : UInt64) (ha : Finite a)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0) (h : Finite (Wasm.IEEE64.mul a b)) : Finite b := by
  by_contra hb
  have he : Wasm.IEEE64.exponent b = 2047 := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq, not_not] at hb
    exact hb
  have ha0' : (Wasm.IEEE64.scaledMagnitude a == 0) = false := beq_false_of_ne ha0
  by_cases hn : Wasm.IEEE64.isNaN b = true
  · have h0 : Wasm.IEEE64.mul a b = Wasm.IEEE64.canonicalNaN := by simp [Wasm.IEEE64.mul, hn]
    rw [h0] at h
    exact absurd h (by unfold CodeLib.IEEE64.Finite; decide)
  · have hf : Wasm.IEEE64.fraction b = 0 := by
      simp only [Wasm.IEEE64.isNaN, he, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
        true_and, not_not] at hn
      exact hn
    have hi : Wasm.IEEE64.isInfinite b = true := by simp [Wasm.IEEE64.isInfinite, he, hf]
    have h0 : Wasm.IEEE64.mul a b =
        Wasm.IEEE64.infinity (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
      simp [Wasm.IEEE64.mul, not_nan_of_finite ha, hn, hi, not_infinite_of_finite ha, ha0']
    rw [h0] at h
    revert h
    cases Wasm.IEEE64.sign a != Wasm.IEEE64.sign b <;> (unfold CodeLib.IEEE64.Finite; decide)

theorem ix_negate (b : UInt64) :
    ((Wasm.IEEE64.negate b >>> 32) &&& (0x7fffffff : UInt64)) =
      ((b >>> 32) &&& (0x7fffffff : UInt64)) := by
  show ErfBranches.ix (Wasm.IEEE64.negate b) = ErfBranches.ix b
  apply UInt64.toNat_inj.mp
  rw [ErfBranches.ix_toNat, ErfBranches.ix_toNat, F64SignedRounding.negate_toNat]
  have hb := b.toNat_lt
  have hsz : UInt64.size = 18446744073709551616 := rfl
  unfold Wasm.IEEE64.sign
  by_cases h1 : 2 ^ 63 ≤ b.toNat
  · simp only [h1, decide_true, ite_true]
    omega
  · simp only [h1, decide_false, Bool.false_eq_true, ite_false]
    omega

theorem neg_toBits (x : Float) (hxf : Finite x.toBits) :
    (-x).toBits = Wasm.IEEE64.negate x.toBits := by
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero, not_nan_of_finite hxf]
  rfl

theorem abs_negate (b : UInt64) : Wasm.IEEE64.abs (Wasm.IEEE64.negate b) = Wasm.IEEE64.abs b := by
  obtain ⟨he, hf, _⟩ := F64Sign.fields_negate b
  simp only [Wasm.IEEE64.abs, he, hf]

theorem value_pos_scaled (a b : UInt64) (h : 0 < value a + value b) :
    Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b ≠ 0 := by
  intro hz
  have : value a + value b = 0 := by
    simp only [value, ← add_div]
    rw [show (Wasm.IEEE64.scaledValue a : ℝ) + Wasm.IEEE64.scaledValue b = 0 by exact_mod_cast hz]
    simp
  linarith

/-- The words below `2^-1015`. -/
theorem sub_negate (P : UInt64) (hP : Finite P) (hp0 : 0 < value P) (hp1 : value P ≤ 1) :
    Wasm.IEEE64.div (Wasm.IEEE64.add (Wasm.IEEE64.mul 0x4020000000000000 (Wasm.IEEE64.negate P))
      (Wasm.IEEE64.mul 0x3FF06EBA8214DB69 (Wasm.IEEE64.negate P))) 0x4020000000000000 =
    Wasm.IEEE64.negate (Wasm.IEEE64.div (Wasm.IEEE64.add (Wasm.IEEE64.mul 0x4020000000000000 P)
      (Wasm.IEEE64.mul 0x3FF06EBA8214DB69 P)) 0x4020000000000000) := by
  have hs := sign_false_of_pos P hp0
  obtain ⟨hAf, hAv⟩ := eight_mul P hP hs hp1
  obtain ⟨hBf, hBe⟩ := efx8_mul P hP hp0 hp1
  obtain ⟨he0, _⟩ := efx_bounds
  have hmin : 1 / (2 : ℝ) ^ 1074 ≤ value P := by
    have hm : 0 < Wasm.IEEE64.scaledMagnitude P := by
      rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude P) with h0 | h0
      · exfalso
        have : value P = 0 := by
          simp only [value, Wasm.IEEE64.scaledValue, h0]
          split <;> simp
        linarith
      · exact h0
    have hv : value P = (Wasm.IEEE64.scaledMagnitude P : ℝ) / 2 ^ 1074 := by
      simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false]
      push_cast
      rfl
    rw [hv]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hm
  have hsum : 0 < value (Wasm.IEEE64.mul 0x4020000000000000 P) +
      value (Wasm.IEEE64.mul 0x3FF06EBA8214DB69 P) := by
    rw [hAv]
    have h1 := (abs_le.mp hBe).1
    have h2 : 1 / (2 : ℝ) ^ 53 * max (8 * efxQ * value P) (1 / 2 ^ 1022) ≤
        1 / 2 ^ 53 * (8 * efxQ * value P + 1 / 2 ^ 1022) :=
      mul_le_mul_of_nonneg_left (max_le (by linarith [show (0 : ℝ) ≤ 1 / 2 ^ 1022 by positivity])
        (by nlinarith)) (by positivity)
    have h3 : (1 : ℝ) / 2 ^ 53 * (8 * efxQ * value P) ≤ 8 * efxQ * value P := by
      have : (0 : ℝ) ≤ 8 * efxQ * value P := by positivity
      nlinarith
    have h4 : (1 : ℝ) / 2 ^ 53 * (1 / 2 ^ 1022) < 8 * (1 / 2 ^ 1074) := by norm_num
    nlinarith
  have hS := F64AddBounds.add_real_relative _ _ hAf hBf (by
    rw [hAv, abs_lt]
    have h1 := (abs_le.mp hBe).2
    have h2 : 1 / (2 : ℝ) ^ 53 * max (8 * efxQ * value P) (1 / 2 ^ 1022) ≤ 1 := by
      have : max (8 * (efxQ : ℝ) * value P) (1 / 2 ^ 1022) ≤ 2 := max_le (by nlinarith) (by norm_num)
      nlinarith
    constructor <;> nlinarith [show (16 : ℝ) < 2 ^ 1023 by norm_num])
  rw [mul_negate_right _ _ eight_finite hP, mul_negate_right _ _ efx8_finite hP,
    add_negate _ _ hAf hBf (value_pos_scaled _ _ hsum),
    div_negate_left _ _ hS.1 eight_finite (by decide +kernel)]

theorem tiny_negate (P : UInt64) (hP : Finite P) (hp0 : 0 < value P) (hp1 : value P ≤ 1) :
    Wasm.IEEE64.add (Wasm.IEEE64.negate P) (Wasm.IEEE64.mul 0x3FC06EBA8214DB69 (Wasm.IEEE64.negate P)) =
      Wasm.IEEE64.negate (Wasm.IEEE64.add P (Wasm.IEEE64.mul 0x3FC06EBA8214DB69 P)) := by
  obtain ⟨he0, he1⟩ := efx_bounds
  have hpb : |value (0x3FC06EBA8214DB69 : UInt64) * value P| < (2 : ℝ) ^ 1022 := by
    rw [efx_value, abs_mul, abs_of_pos he0, abs_of_pos hp0]
    nlinarith [show (1 : ℝ) < 2 ^ 1022 by norm_num]
  obtain ⟨hpf, hpe⟩ := F64MulBounds.mul_real_mixed _ P efx_finite hP hpb
  have hmin : 1 / (2 : ℝ) ^ 1074 ≤ value P := by
    have hs := sign_false_of_pos P hp0
    have hm : 0 < Wasm.IEEE64.scaledMagnitude P := by
      rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude P) with h0 | h0
      · exfalso
        have : value P = 0 := by
          simp only [value, Wasm.IEEE64.scaledValue, h0]
          split <;> simp
        linarith
      · exact h0
    have hv : value P = (Wasm.IEEE64.scaledMagnitude P : ℝ) / 2 ^ 1074 := by
      simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false]
      push_cast
      rfl
    rw [hv]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hm
  have hsum : 0 < value P + value (Wasm.IEEE64.mul 0x3FC06EBA8214DB69 P) := by
    rw [efx_value, abs_mul, abs_of_pos he0, abs_of_pos hp0] at hpe
    have h1 := (abs_le.mp hpe).1
    have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
    have he : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := by
      norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
    rw [hu, he] at h1
    have h2 : (1 : ℝ) / 2 ^ 53 * (efxQ * value P) ≤ efxQ * value P := by
      have : (0 : ℝ) ≤ efxQ * value P := by positivity
      nlinarith
    have h3 : (1 : ℝ) / 2 ^ 1075 < 1 / 2 ^ 1074 := by norm_num
    linarith
  rw [mul_negate_right _ _ efx_finite hP, add_negate _ _ hP hpf (value_pos_scaled _ _ hsum)]

#print axioms reference_le_two
#print axioms finite_of_within_add
#print axioms add_ne_zero_of_within
#print axioms finite_of_mul_finite
#print axioms ix_negate
#print axioms sub_negate
#print axioms tiny_negate

end Verified.Examples.ErfNegative
