import LeanExe.ProofKit.F64Approx

namespace Verified.Examples.FourierProduct
open CodeLib.IEEE64 LeanExe.ProofKit.F64Approx

noncomputable def productMagnitude (A B : ℝ) : ℝ :=
  (1 + unitRoundoff64) ^ 2 * (1 + 32 * unitRoundoff64) * (|A| + |B|) +
    2 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon

noncomputable def productError (A B : ℝ) : ℝ :=
  ((1 + unitRoundoff64) ^ 2 * (1 + 32 * unitRoundoff64) - 1) * (|A| + |B|) +
    2 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon

private noncomputable def mulFactor : ℝ :=
  (1 + unitRoundoff64) * (1 + 32 * unitRoundoff64)

private noncomputable def mulError (A : ℝ) : ℝ :=
  (mulFactor - 1) * |A| + multiplicationUnderflowEpsilon

private noncomputable def sumMagnitude (A B : ℝ) : ℝ :=
  mulFactor * (|A| + |B|) + 2 * multiplicationUnderflowEpsilon

private theorem unit_nonneg : 0 ≤ unitRoundoff64 := by
  unfold unitRoundoff64
  exact one_div_nonneg.mpr (pow_nonneg (by norm_num) _)

private theorem eta_nonneg : 0 ≤ multiplicationUnderflowEpsilon := by
  unfold multiplicationUnderflowEpsilon
  exact one_div_nonneg.mpr (pow_nonneg (by norm_num) _)

theorem productMagnitude_nonneg (A B : ℝ) : 0 ≤ productMagnitude A B := by
  unfold productMagnitude
  have hu := unit_nonneg
  have heta := eta_nonneg
  have hu1 : 0 ≤ 1 + unitRoundoff64 := by linarith only [hu]
  have hd1 : 0 ≤ 1 + 32 * unitRoundoff64 := by linarith only [hu]
  exact add_nonneg
    (mul_nonneg (mul_nonneg (pow_nonneg hu1 _) hd1) (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    (mul_nonneg (mul_nonneg (by norm_num) hu1) heta)

theorem productMagnitude_eq (A B : ℝ) :
    productMagnitude A B = |A| + |B| + productError A B := by
  unfold productMagnitude productError
  ring

private theorem scalar_bound (A B : ℝ) :
    |A| * (1 + 32 * unitRoundoff64) ≤ productMagnitude A B := by
  have hu := unit_nonneg
  have heta := eta_nonneg
  have hu1 : 0 ≤ 1 + unitRoundoff64 := by linarith only [hu]
  have hd1 : 0 ≤ 1 + 32 * unitRoundoff64 := by linarith only [hu]
  have hpow : 1 ≤ (1 + unitRoundoff64) ^ 2 := one_le_pow₀ (by linarith)
  have hfactor : 1 + 32 * unitRoundoff64 ≤
      (1 + unitRoundoff64) ^ 2 * (1 + 32 * unitRoundoff64) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hpow hd1
  calc
    _ = (1 + 32 * unitRoundoff64) * |A| := mul_comm _ _
    _ ≤ ((1 + unitRoundoff64) ^ 2 * (1 + 32 * unitRoundoff64)) * |A| :=
      mul_le_mul_of_nonneg_right hfactor (abs_nonneg A)
    _ ≤ ((1 + unitRoundoff64) ^ 2 * (1 + 32 * unitRoundoff64)) * (|A| + |B|) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg B))
        (mul_nonneg (pow_nonneg hu1 _) hd1)
    _ ≤ productMagnitude A B := by
      unfold productMagnitude
      exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hu1) heta)

private theorem sum_bound (A B : ℝ) : sumMagnitude A B ≤ productMagnitude A B := by
  have hu := unit_nonneg
  have heta := eta_nonneg
  have hu1 : 0 ≤ 1 + unitRoundoff64 := by linarith only [hu]
  have hd1 : 0 ≤ 1 + 32 * unitRoundoff64 := by linarith only [hu]
  have hsum : 0 ≤ sumMagnitude A B := by
    unfold sumMagnitude mulFactor
    exact add_nonneg
      (mul_nonneg (mul_nonneg hu1 hd1) (add_nonneg (abs_nonneg _) (abs_nonneg _)))
      (mul_nonneg (by norm_num) heta)
  calc
    sumMagnitude A B ≤ (1 + unitRoundoff64) * sumMagnitude A B := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show 1 ≤ 1 + unitRoundoff64 by linarith) hsum
    _ = productMagnitude A B := by unfold sumMagnitude mulFactor productMagnitude; ring

private theorem mul_near (a c : Float) (C : ℝ) (ha : Finite a.toBits)
    (hc : FApprox c C (32 * unitRoundoff64)) (hC : |C| ≤ 1)
    (hsafe : |value a.toBits| * (1 + 32 * unitRoundoff64) < (2 : ℝ) ^ 1022) :
    FApprox (a * c) (value a.toBits * C) (mulError (value a.toBits)) := by
  have ha0 : FApprox a (value a.toBits) 0 := approx_self _ ha
  have h := fapprox_mul ha0 hc |value a.toBits| 1 le_rfl hC
    (|value a.toBits| * (1 + 32 * unitRoundoff64)) (by simp) hsafe
  exact h.mono (le_of_eq (by
    rw [show (1 : ℝ) / 2 ^ 1075 = multiplicationUnderflowEpsilon from rfl]
    unfold mulError mulFactor unitRoundoff64
    ring))

private theorem target_norm (A B C D : ℝ) (hC : |C| ≤ 1) (hD : |D| ≤ 1) :
    |A * C| + |B * D| ≤ |A| + |B| := by
  rw [abs_mul, abs_mul]
  simpa only [mul_one] using add_le_add
    (mul_le_mul_of_nonneg_left hC (abs_nonneg A))
    (mul_le_mul_of_nonneg_left hD (abs_nonneg B))

private theorem pair_products (a b c d : Float) (C D : ℝ)
    (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hc : FApprox c C (32 * unitRoundoff64)) (hd : FApprox d D (32 * unitRoundoff64))
    (hC : |C| ≤ 1) (hD : |D| ≤ 1)
    (hsafe : productMagnitude (value a.toBits) (value b.toBits) < (2 : ℝ) ^ 1022) :
    FApprox (a * c) (value a.toBits * C) (mulError (value a.toBits)) ∧
    FApprox (b * d) (value b.toBits * D) (mulError (value b.toBits)) ∧
    |value a.toBits * C| + |value b.toBits * D| ≤ |value a.toBits| + |value b.toBits| ∧
    sumMagnitude (value a.toBits) (value b.toBits) < (2 : ℝ) ^ 1023 := by
  refine ⟨mul_near a c C ha hc hC ((scalar_bound _ _).trans_lt hsafe),
    mul_near b d D hb hd hD ?_, target_norm _ _ _ _ hC hD, ?_⟩
  · have hsym : productMagnitude (value b.toBits) (value a.toBits) =
        productMagnitude (value a.toBits) (value b.toBits) := by
      unfold productMagnitude
      rw [add_comm |value b.toBits| |value a.toBits|]
    exact (scalar_bound _ _).trans_lt (by rw [hsym]; exact hsafe)
  · exact ((sum_bound _ _).trans_lt hsafe).trans
      (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : 1022 < 1023))

private theorem sumMagnitude_eq (A B : ℝ) :
    |A| + |B| + (mulError A + mulError B) = sumMagnitude A B := by
  unfold mulError sumMagnitude
  ring

private theorem productError_eq (A B : ℝ) :
    mulError A + mulError B + sumMagnitude A B / 2 ^ 53 = productError A B := by
  unfold mulError sumMagnitude mulFactor productError unitRoundoff64
  ring

theorem sub_near (a b c d : Float) (C D : ℝ)
    (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hc : FApprox c C (32 * unitRoundoff64)) (hd : FApprox d D (32 * unitRoundoff64))
    (hC : |C| ≤ 1) (hD : |D| ≤ 1)
    (hsafe : productMagnitude (value a.toBits) (value b.toBits) < (2 : ℝ) ^ 1022) :
    FApprox (a * c - b * d) (value a.toBits * C - value b.toBits * D)
      (productError (value a.toBits) (value b.toBits)) := by
  obtain ⟨hac, hbd, hnorm, hcap⟩ := pair_products a b c d C D ha hb hc hd hC hD hsafe
  have hbound : |value a.toBits * C - value b.toBits * D| +
      (mulError (value a.toBits) + mulError (value b.toBits)) ≤
      sumMagnitude (value a.toBits) (value b.toBits) := by
    rw [← sumMagnitude_eq]
    exact add_le_add ((abs_sub _ _).trans hnorm) le_rfl
  have h := fapprox_sub hac hbd (sumMagnitude (value a.toBits) (value b.toBits)) hbound hcap
  exact h.mono (le_of_eq (productError_eq _ _))

theorem add_near (a b c d : Float) (C D : ℝ)
    (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hc : FApprox c C (32 * unitRoundoff64)) (hd : FApprox d D (32 * unitRoundoff64))
    (hC : |C| ≤ 1) (hD : |D| ≤ 1)
    (hsafe : productMagnitude (value a.toBits) (value b.toBits) < (2 : ℝ) ^ 1022) :
    FApprox (a * c + b * d) (value a.toBits * C + value b.toBits * D)
      (productError (value a.toBits) (value b.toBits)) := by
  obtain ⟨hac, hbd, hnorm, hcap⟩ := pair_products a b c d C D ha hb hc hd hC hD hsafe
  have hbound : |value a.toBits * C + value b.toBits * D| +
      (mulError (value a.toBits) + mulError (value b.toBits)) ≤
      sumMagnitude (value a.toBits) (value b.toBits) := by
    rw [← sumMagnitude_eq]
    exact add_le_add ((abs_add_le _ _).trans hnorm) le_rfl
  have h := fapprox_add hac hbd (sumMagnitude (value a.toBits) (value b.toBits)) hbound hcap
  exact h.mono (le_of_eq (productError_eq _ _))

theorem sub_magnitude (a b c d : Float) (C D : ℝ)
    (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hc : FApprox c C (32 * unitRoundoff64)) (hd : FApprox d D (32 * unitRoundoff64))
    (hC : |C| ≤ 1) (hD : |D| ≤ 1)
    (hsafe : productMagnitude (value a.toBits) (value b.toBits) < (2 : ℝ) ^ 1022) :
    |value (a * c - b * d).toBits| ≤ productMagnitude (value a.toBits) (value b.toBits) := by
  have h := sub_near a b c d C D ha hb hc hd hC hD hsafe
  rw [productMagnitude_eq]
  exact h.mag.trans (add_le_add
    ((abs_sub _ _).trans (target_norm _ _ _ _ hC hD)) le_rfl)

theorem add_magnitude (a b c d : Float) (C D : ℝ)
    (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hc : FApprox c C (32 * unitRoundoff64)) (hd : FApprox d D (32 * unitRoundoff64))
    (hC : |C| ≤ 1) (hD : |D| ≤ 1)
    (hsafe : productMagnitude (value a.toBits) (value b.toBits) < (2 : ℝ) ^ 1022) :
    |value (a * c + b * d).toBits| ≤ productMagnitude (value a.toBits) (value b.toBits) := by
  have h := add_near a b c d C D ha hb hc hd hC hD hsafe
  rw [productMagnitude_eq]
  exact h.mag.trans (add_le_add
    ((abs_add_le _ _).trans (target_norm _ _ _ _ hC hD)) le_rfl)

#print axioms sub_near
#print axioms add_near
#print axioms sub_magnitude
#print axioms add_magnitude

end Verified.Examples.FourierProduct
