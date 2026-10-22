import Library.Numerics.Float64.Tanh.TanhSmall

/-!
The branch `1 ≤ abs(x) < 22` of fdlibm's `tanh`, which returns `1 - 2 / (t + 2)` with
`t = expm1(2 abs(x))`, within one step of `tanh abs(x) = 1 - 2 / (T + 2)`, `T = exp(2 abs(x)) - 1`.
With `t` within `1.851 u T` of `T`, the rounded `t + 2` and the rounded quotient leave
`1 - q` within `7.704 u / D + η` of the result, below the spacing `u` of `[1/2, 1)` for
`T ≥ 6.38`.
-/

namespace Library.Numerics.Float64.Tanh.TanhLarge
open CodeLib.IEEE64 LeanExe.ProofKit TanhWords

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem large_core (c : UInt64) (hcf : Finite c) (S T : ℝ) (hT : 638 / 100 ≤ T)
    (hT2 : T ≤ 2 ^ 80) (hc1 : |value c - S| ≤ u * S)
    (hS : |S - T| ≤ 85 / 100 * u * T) :
    F64SignedRounding.WithinSteps 1 (1 - 2 / (T + 2))
      (Wasm.IEEE64.sub Expm1Words.one
        (Wasm.IEEE64.div Expm1Words.two (Wasm.IEEE64.add c Expm1Words.two))) := by
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hη : η = 1 / 2 ^ 1075 := Expm1KernelInner.eta_value
  have htwo : value Expm1Words.two = 2 := Expm1KernelInner.const_values.2.2.1
  have h2f : Finite Expm1Words.two := Expm1KernelInner.const_finite.2.2.1
  have hone : value Expm1Words.one = 1 := Expm1KernelInner.const_values.1
  have h1f : Finite Expm1Words.one := Expm1KernelInner.const_finite.1
  rw [hu] at hc1 hS
  have hc1b := abs_le.mp hc1
  have hSb := abs_le.mp hS
  -- `abs(C - T) ≤ 1.851 u T`.
  have hCT : |value c - T| ≤ 1851 / 1000 * (1 / 2 ^ 53) * T := by
    rw [abs_le]; constructor <;> nlinarith
  have hCTb := abs_le.mp hCT
  have hC0 : 0 < value c + 2 := by nlinarith
  have hCu : value c + 2 < 2 ^ 81 := by nlinarith
  -- `d = c + 2`.
  have hd := F64AddBounds.add_real_relative c Expm1Words.two hcf h2f (by
    rw [htwo, abs_of_pos hC0]
    calc value c + 2 < 2 ^ 81 := hCu
      _ ≤ 2 ^ 1023 := pow_le_pow_right₀ (by norm_num) (by norm_num))
  rw [htwo, abs_of_pos hC0, hu] at hd
  have hdb := abs_le.mp hd.2
  have hDT : |value (Wasm.IEEE64.add c Expm1Words.two) - (T + 2)| ≤
      2852 / 1000 * (1 / 2 ^ 53) * T + 2 * (1 / 2 ^ 53) := by
    rw [abs_le]; constructor <;> nlinarith
  have hDTb := abs_le.mp hDT
  have hD0 : 836 / 100 ≤ value (Wasm.IEEE64.add c Expm1Words.two) := by nlinarith
  have hDpos : 0 < value (Wasm.IEEE64.add c Expm1Words.two) := by linarith
  -- `q = 2 / d`.
  have hdm : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.add c Expm1Words.two) ≠ 0 := by
    have hm := Expm1Theorem.magnitude_pos _ (by rw [abs_of_pos hDpos]; exact hDpos)
    omega
  have hq := F64DivBounds.div_real_mixed Expm1Words.two _ h2f hd.1 hdm (by
    rw [htwo, abs_div, abs_two, abs_of_pos hDpos, div_lt_iff₀ hDpos]
    have : (1 : ℝ) ≤ 2 ^ 1022 := one_le_pow₀ (by norm_num)
    nlinarith)
  rw [htwo, abs_div, abs_two, abs_of_pos hDpos, hu, hη] at hq
  have hqb := abs_le.mp hq.2
  have h2D0 : 0 < 2 / value (Wasm.IEEE64.add c Expm1Words.two) := by positivity
  have h2D : 2 / value (Wasm.IEEE64.add c Expm1Words.two) ≤ 2 / (836 / 100) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hD0
  have h4 : (2 : ℝ) / (836 / 100) ≤ 1 / 4 := by norm_num
  have hsm : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 10 := by norm_num
  have hQ1 : value (Wasm.IEEE64.div Expm1Words.two (Wasm.IEEE64.add c Expm1Words.two)) < 1 / 2 := by
    linarith
  have hQ0 : -1 < value (Wasm.IEEE64.div Expm1Words.two (Wasm.IEEE64.add c Expm1Words.two)) := by
    linarith
  have hnear := F64NearestSum.sub_nearest Expm1Words.one _ h1f hq.1 (by rw [hone]; linarith)
    (by rw [hone]; have : (1 : ℝ) ≤ 2 ^ 1023 := one_le_pow₀ (by norm_num)
        linarith)
  rw [hone] at hnear
  have hT2' : 0 < T + 2 := by linarith
  refine F64NearestSteps.within_of_interior _ _ _ 1022 (by norm_num) (by norm_num) ?_ ?_ hnear ?_
  · have h1 : ((2 : ℝ) ^ (1022 + 51) + 2 * 2 ^ (1022 - 1)) / 2 ^ 1074 = 1 / 2 + 1 / 2 ^ 52 := by
      norm_num
    rw [h1]
    have : 2 / (T + 2) ≤ 2 / (838 / 100) := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by linarith)
    have : (2 : ℝ) / (838 / 100) ≤ 1 / 2 - 1 / 2 ^ 52 := by norm_num
    linarith
  · have : 0 < 2 / (T + 2) := by positivity
    have : (1 : ℝ) < F64PositiveRounding.overflowThreshold := by
      unfold F64PositiveRounding.overflowThreshold; norm_num
    linarith
  · have h1 : (2 : ℝ) ^ (1022 - 1) / 2 ^ 1074 = 1 / 2 ^ 53 := by norm_num
    rw [h1]
    generalize hD : value (Wasm.IEEE64.add c Expm1Words.two) = D at *
    generalize hQ : value (Wasm.IEEE64.div Expm1Words.two (Wasm.IEEE64.add c Expm1Words.two)) = Q
      at *
    have hsplit : 1 - Q - (1 - 2 / (T + 2)) = -((Q - 2 / D) + (2 / D - 2 / (T + 2))) := by ring
    rw [hsplit, abs_neg]
    have hdiff : |2 / D - 2 / (T + 2)| ≤ 5704 / 1000 * (1 / 2 ^ 53) / D := by
      have he : 2 / D - 2 / (T + 2) = 2 * ((T + 2) - D) / (D * (T + 2)) := by
        field_simp
      rw [he, abs_div, abs_mul, abs_two, abs_of_pos (by positivity : (0 : ℝ) < D * (T + 2)),
        div_le_div_iff₀ (by positivity) hDpos, abs_sub_comm]
      have h3 : 2 * (2852 / 1000 * (1 / 2 ^ 53) * T + 2 * (1 / 2 ^ 53)) ≤
          5704 / 1000 * (1 / 2 ^ 53) * (T + 2) := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left hDT (by norm_num : (0 : ℝ) ≤ 2)
      calc 2 * |D - (T + 2)| * D ≤ 5704 / 1000 * (1 / 2 ^ 53) * (T + 2) * D :=
            mul_le_mul_of_nonneg_right (h4.trans h3) hDpos.le
        _ = 5704 / 1000 * (1 / 2 ^ 53) * (D * (T + 2)) := by ring
    have hsum : |(Q - 2 / D) + (2 / D - 2 / (T + 2))| ≤
        1 / 2 ^ 53 * (2 / D) + 1 / 2 ^ 1075 + 5704 / 1000 * (1 / 2 ^ 53) / D := by
      refine (abs_add_le _ _).trans (add_le_add ?_ hdiff)
      rw [abs_le]; constructor <;> linarith
    have h5 : 1 / 2 ^ 53 * (2 / D) + 5704 / 1000 * (1 / 2 ^ 53) / D =
        7704 / 1000 * (1 / 2 ^ 53) / D := by ring
    have h6 : 7704 / 1000 * (1 / 2 ^ 53) / D ≤ 7704 / 1000 * (1 / 2 ^ 53) / (836 / 100) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hD0
    have h7 : (7704 : ℝ) / 1000 * (1 / 2 ^ 53) / (836 / 100) + 1 / 2 ^ 1075 < 1 / 2 ^ 53 := by
      norm_num
    linarith

#print axioms large_core

end Library.Numerics.Float64.Tanh.TanhLarge
