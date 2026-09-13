import Project.ProofKit.F64ArithmeticBounds

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds

set_option exponentiation.threshold 4096

theorem side_flux_terms (velocity transport transverse energy pressure : UInt64)
    (hv : Finite velocity) (ht : Finite transport) (hy : Finite transverse)
    (he : Finite energy) (hp : Finite pressure)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (bv : |value velocity| ≤ 2 * M^2) (bt : |value transport| ≤ 2 * M^3)
    (byy : |value transverse| ≤ M) (be : |value energy| ≤ M)
    (bp : |value pressure| ≤ 5 * M^3) :
    let momentumFlux := Wasm.IEEE64.add transport pressure
    let transverseFlux := Wasm.IEEE64.mul transverse velocity
    let enthalpy := Wasm.IEEE64.add energy pressure
    let energyFlux := Wasm.IEEE64.mul velocity enthalpy
    Finite momentumFlux ∧ Finite transverseFlux ∧ Finite enthalpy ∧ Finite energyFlux ∧
    |value momentumFlux| ≤ 8 * M^3 ∧ |value transverseFlux| ≤ 3 * M^3 ∧
    |value enthalpy| ≤ 7 * M^3 ∧ |value energyFlux| ≤ 15 * M^5 ∧
    |value momentumFlux - (value transport + value pressure)| ≤ 7 * arithmeticEpsilon * M^3 ∧
    |value transverseFlux - value transverse * value velocity| ≤ 2 * arithmeticEpsilon * M^3 ∧
    |value enthalpy - (value energy + value pressure)| ≤ 6 * arithmeticEpsilon * M^3 ∧
    |value energyFlux - value velocity * value enthalpy| ≤ 14 * arithmeticEpsilon * M^5 := by
  let momentumFlux := Wasm.IEEE64.add transport pressure
  let transverseFlux := Wasm.IEEE64.mul transverse velocity
  let enthalpy := Wasm.IEEE64.add energy pressure
  let energyFlux := Wasm.IEEE64.mul velocity enthalpy
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM3 : 1 ≤ M^3 := one_le_pow₀ hM
  have hM5 : 1 ≤ M^5 := one_le_pow₀ hM
  have hM13 : M ≤ M^3 := by
    have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^2) hMpos.le
    nlinarith only [h]
  have hM35 : M^3 ≤ M^5 := by
    have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^2) (pow_nonneg hMpos.le 3)
    nlinarith only [h]
  have hmax : 32 * M^5 < (2 : ℝ)^1022 := by
    calc
      _ ≤ 32 * ((2 : ℝ)^100)^5 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMmax 5) (by norm_num)
      _ < (2 : ℝ)^1022 := by norm_num
  have hmaxAdd : 32 * M^5 < (2 : ℝ)^1023 := hmax.trans (by norm_num)
  have heps3 := mul_le_mul_of_nonneg_right epsilon_small.le (pow_nonneg hMpos.le 3)
  have heps5 := mul_le_mul_of_nonneg_right epsilon_small.le (pow_nonneg hMpos.le 5)
  have bm : |value transport + value pressure| ≤ 7 * M^3 := by
    have h := abs_add_le (value transport) (value pressure)
    linarith only [h, bt, bp]
  obtain ⟨hfm, em⟩ := add_error transport pressure ht hp (7 * M^3)
    (by linarith only [hM3]) (by linarith only [hmaxAdd, hM35, hM3]) bm
  have bmRounded : |value momentumFlux| ≤ 8 * M^3 := by
    have h := magnitude_of_error _ _ _ _ em bm
    change |value momentumFlux| ≤ 7 * M^3 + arithmeticEpsilon * (7 * M^3) at h
    nlinarith only [h, heps3, hM3]
  have btrans : |value transverse * value velocity| ≤ 2 * M^3 := by
    rw [abs_mul]
    calc
      _ ≤ M * (2 * M^2) := mul_le_mul byy bv (abs_nonneg _) hMpos.le
      _ = 2 * M^3 := by ring
  obtain ⟨hft, et⟩ := mul_error transverse velocity hy hv (2 * M^3)
    (by linarith only [hM3]) (by linarith only [hmax, hM35, hM3]) btrans
  have btRounded : |value transverseFlux| ≤ 3 * M^3 := by
    have h := magnitude_of_error _ _ _ _ et btrans
    change |value transverseFlux| ≤ 2 * M^3 + arithmeticEpsilon * (2 * M^3) at h
    nlinarith only [h, heps3, hM3]
  have benth : |value energy + value pressure| ≤ 6 * M^3 := by
    have h := abs_add_le (value energy) (value pressure)
    linarith only [h, be, bp, hM13]
  obtain ⟨hfh, eh⟩ := add_error energy pressure he hp (6 * M^3)
    (by linarith only [hM3]) (by linarith only [hmaxAdd, hM35, hM3]) benth
  have bhRounded : |value enthalpy| ≤ 7 * M^3 := by
    have h := magnitude_of_error _ _ _ _ eh benth
    change |value enthalpy| ≤ 6 * M^3 + arithmeticEpsilon * (6 * M^3) at h
    nlinarith only [h, heps3, hM3]
  have benergy : |value velocity * value enthalpy| ≤ 14 * M^5 := by
    rw [abs_mul]
    calc
      _ ≤ (2 * M^2) * (7 * M^3) := mul_le_mul bv bhRounded (abs_nonneg _) (by positivity)
      _ = 14 * M^5 := by ring
  obtain ⟨hfe, ee⟩ := mul_error velocity enthalpy hv hfh (14 * M^5)
    (by linarith only [hM5]) (by linarith only [hmax, hM5]) benergy
  have beRounded : |value energyFlux| ≤ 15 * M^5 := by
    have h := magnitude_of_error _ _ _ _ ee benergy
    change |value energyFlux| ≤ 14 * M^5 + arithmeticEpsilon * (14 * M^5) at h
    nlinarith only [h, heps5, hM5]
  refine ⟨hfm, hft, hfh, hfe, bmRounded, btRounded, bhRounded, beRounded, ?_, ?_, ?_, ?_⟩
  · exact em.trans_eq (by ring)
  · exact et.trans_eq (by ring)
  · exact eh.trans_eq (by ring)
  · exact ee.trans_eq (by ring)

#print axioms side_flux_terms
end Project.EulerRiemann.Numerics
