import LeanExe.ProofKit.F64Approx

namespace Verified.Examples.FourierPowerArithmetic
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx

noncomputable def squareMagnitude (M : ℝ) : ℝ :=
  (1 + unitRoundoff64) * M ^ 2 + multiplicationUnderflowEpsilon

noncomputable def powerError (L E : ℝ) : ℝ :=
  4 * L * E + 2 * E ^ 2 + 2 * unitRoundoff64 * (2 + unitRoundoff64) * (L + E) ^ 2 +
    2 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon

private noncomputable def squareError (L E : ℝ) : ℝ :=
  2 * L * E + E ^ 2 + unitRoundoff64 * (L + E) ^ 2 + multiplicationUnderflowEpsilon

private theorem unit_nonneg : 0 ≤ unitRoundoff64 := by
  unfold unitRoundoff64
  exact one_div_nonneg.mpr (pow_nonneg (by norm_num) _)

private theorem eta_nonneg : 0 ≤ multiplicationUnderflowEpsilon := by
  unfold multiplicationUnderflowEpsilon
  exact one_div_nonneg.mpr (pow_nonneg (by norm_num) _)

theorem square_le_squareMagnitude (M : ℝ) : M ^ 2 ≤ squareMagnitude M := by
  unfold squareMagnitude
  have h := mul_nonneg unit_nonneg (sq_nonneg M)
  linarith only [h, eta_nonneg]

theorem magnitude_safe (M : ℝ) (hM : 0 ≤ M)
    (hsafe : squareMagnitude M < (2 : ℝ) ^ 1022) : M < (2 : ℝ) ^ 1022 := by
  have hsq := (square_le_squareMagnitude M).trans_lt hsafe
  have hcap : (1 : ℝ) < 2 ^ 1022 := one_lt_pow₀ (by norm_num) (by omega)
  by_cases hsmall : M ≤ 1
  · exact hsmall.trans_lt hcap
  · have hmul := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hsmall)) hM
    exact (show M ≤ M ^ 2 by nlinarith only [hmul]).trans_lt hsq

private theorem square_near (a : Float) (A L E : ℝ)
    (ha : FApprox a A E) (hA : |A| ≤ L)
    (hsafe : squareMagnitude (L + E) < (2 : ℝ) ^ 1022) :
    FApprox (a * a) (A ^ 2) (squareError L E) := by
  have h := fapprox_mul ha ha L L hA hA ((L + E) ^ 2)
    (le_of_eq (by ring)) ((square_le_squareMagnitude _).trans_lt hsafe)
  refine (h.congr (by ring)).mono (le_of_eq ?_)
  rw [show (1 : ℝ) / 2 ^ 1075 = multiplicationUnderflowEpsilon from rfl]
  unfold squareError unitRoundoff64
  ring

private theorem square_bound (A L : ℝ) (hA : |A| ≤ L) : A ^ 2 ≤ L ^ 2 := by
  have hL : 0 ≤ L := (abs_nonneg A).trans hA
  have h := mul_le_mul hA hA (abs_nonneg A) hL
  nlinarith only [h, sq_abs A]

private theorem addition_bound (A B L E : ℝ) (hA : |A| ≤ L) (hB : |B| ≤ L) :
    |A ^ 2 + B ^ 2| + (squareError L E + squareError L E) ≤
      2 * squareMagnitude (L + E) := by
  rw [abs_of_nonneg (add_nonneg (sq_nonneg A) (sq_nonneg B))]
  unfold squareError squareMagnitude
  nlinarith only [square_bound A L hA, square_bound B L hB]

private theorem addition_safe (M : ℝ) (hsafe : squareMagnitude M < (2 : ℝ) ^ 1022) :
    2 * squareMagnitude M < (2 : ℝ) ^ 1023 := by
  have hpow : (2 : ℝ) ^ 1023 = 2 * (2 : ℝ) ^ 1022 := by
    rw [show 1023 = 1022 + 1 from rfl, pow_succ]
    exact mul_comm _ _
  rw [hpow]
  exact mul_lt_mul_of_pos_left hsafe (by norm_num)

theorem square_sum_near (a b : Float) (A B L E : ℝ)
    (ha : FApprox a A E) (hb : FApprox b B E) (hA : |A| ≤ L) (hB : |B| ≤ L)
    (hsafe : squareMagnitude (L + E) < (2 : ℝ) ^ 1022) :
    FApprox (a * a + b * b) (A ^ 2 + B ^ 2) (powerError L E) := by
  have ha2 := square_near a A L E ha hA hsafe
  have hb2 := square_near b B L E hb hB hsafe
  have h := fapprox_add ha2 hb2 (2 * squareMagnitude (L + E))
    (addition_bound A B L E hA hB) (addition_safe _ hsafe)
  refine h.mono (le_of_eq ?_)
  unfold squareError squareMagnitude powerError unitRoundoff64
  ring

private theorem square_nonneg (a : Float) (ha : Finite a.toBits)
    (hbound : |value a.toBits * value a.toBits| < (2 : ℝ) ^ 1022) :
    0 ≤ value (a * a).toBits := by
  let n := Wasm.IEEE64.scaledMagnitude a.toBits * Wasm.IEEE64.scaledMagnitude a.toBits
  have hn : n < 2 ^ 3170 := by
    rw [F64MulBounds.product_abs_scaled] at hbound
    change (n : ℝ) / (2 : ℝ) ^ 2148 < (2 : ℝ) ^ 1022 at hbound
    have h := (div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mp hbound
    rw [← pow_add] at h
    exact (Nat.cast_lt (α := ℝ)).mp (by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using h)
  have hs := F64DyadicBounds.dyadic_relative false n hn
  have hroundsign := hs.2.1
  dsimp only [n] at hroundsign
  have hsign : (Wasm.IEEE64.sign a.toBits != Wasm.IEEE64.sign a.toBits) = false := by
    cases Wasm.IEEE64.sign a.toBits <;> rfl
  rw [F64Bits.toBits_mul, mul_finite_rounder _ _ ha ha, hsign]
  simp only [value, Wasm.IEEE64.scaledValue, hroundsign, Bool.false_eq_true, ite_false,
    Int.cast_natCast]
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

theorem square_sum_nonneg (a b : Float) (A B L E : ℝ)
    (ha : FApprox a A E) (hb : FApprox b B E) (hA : |A| ≤ L) (hB : |B| ≤ L)
    (hsafe : squareMagnitude (L + E) < (2 : ℝ) ^ 1022) :
    0 ≤ value (a * a + b * b).toBits := by
  have haMag : |value a.toBits| ≤ L + E := ha.mag.trans (add_le_add hA le_rfl)
  have hbMag : |value b.toBits| ≤ L + E := hb.mag.trans (add_le_add hB le_rfl)
  have haBound : |value a.toBits * value a.toBits| < (2 : ℝ) ^ 1022 := by
    rw [← pow_two, abs_of_nonneg (sq_nonneg _)]
    exact (square_bound _ _ haMag).trans_lt ((square_le_squareMagnitude _).trans_lt hsafe)
  have hbBound : |value b.toBits * value b.toBits| < (2 : ℝ) ^ 1022 := by
    rw [← pow_two, abs_of_nonneg (sq_nonneg _)]
    exact (square_bound _ _ hbMag).trans_lt ((square_le_squareMagnitude _).trans_lt hsafe)
  have ha0 := square_nonneg a ha.1 haBound
  have hb0 := square_nonneg b hb.1 hbBound
  have ha2 := square_near a A L E ha hA hsafe
  have hb2 := square_near b B L E hb hB hsafe
  have hsum : |value (a * a).toBits + value (b * b).toBits| ≤
      2 * squareMagnitude (L + E) := by
    rw [abs_of_nonneg (add_nonneg ha0 hb0)]
    have haUp := ha2.mag
    have hbUp := hb2.mag
    rw [abs_of_nonneg ha0, abs_of_nonneg (sq_nonneg A)] at haUp
    rw [abs_of_nonneg hb0, abs_of_nonneg (sq_nonneg B)] at hbUp
    have h := addition_bound A B L E hA hB
    rw [abs_of_nonneg (add_nonneg (sq_nonneg A) (sq_nonneg B))] at h
    linarith only [haUp, hbUp, h]
  have hr := F64AddBounds.add_real_relative (a * a).toBits (b * b).toBits ha2.1 hb2.1
    (hsum.trans_lt (addition_safe _ hsafe))
  rw [← F64Bits.toBits_add, abs_of_nonneg (add_nonneg ha0 hb0)] at hr
  have hlo := (abs_le.mp hr.2).1
  have hu : unitRoundoff64 ≤ 1 := by norm_num [unitRoundoff64]
  have hunit := mul_le_mul_of_nonneg_right hu (add_nonneg ha0 hb0)
  linarith only [hlo, hunit]

#print axioms square_sum_near
#print axioms square_sum_nonneg
#print axioms magnitude_safe

end Verified.Examples.FourierPowerArithmetic
