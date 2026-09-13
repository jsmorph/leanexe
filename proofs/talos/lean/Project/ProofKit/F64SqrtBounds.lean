import Project.ProofKit.F64SqrtRounding
import Project.ProofKit.F64NormalizeTiny

namespace Project.ProofKit.F64SqrtBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem sqrt_real_relative (a : UInt64) (ha : Finite a)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hsign : Wasm.IEEE64.sign a = false) :
    Finite (Wasm.IEEE64.sqrt a) ∧
    |value (Wasm.IEEE64.sqrt a) - Real.sqrt (value a)| ≤
      unitRoundoff64 * Real.sqrt (value a) := by
  let magnitude := Wasm.IEEE64.scaledMagnitude a
  let result := Wasm.IEEE64.roundSqrtMagnitude magnitude
  have hmax : magnitude < 2^2098 :=
    (F64NormalizeTiny.scaledMagnitude_bound a).trans_le
      (Nat.pow_le_pow_right (by omega)
        (by have := F64Admissibility.finite_exponent_bound a ha; omega))
  have hs := F64SqrtRounding.sqrt_relative magnitude ha0 hmax
  rw [sqrt_positive_finite a ha ha0 hsign]
  refine ⟨hs.1, ?_⟩
  have hscalePos : (0 : ℝ) < (2 : ℝ)^1074 := by positivity
  have hsqrtScale : Real.sqrt ((2 : ℝ)^1074) = (2 : ℝ)^537 := by
    rw [show (2 : ℝ)^1074 = ((2 : ℝ)^537)^2 by rw [← pow_mul]]
    exact Real.sqrt_sq (by positivity)
  have hsqrtScaled : Real.sqrt ((magnitude : ℝ) / (2 : ℝ)^1074) =
      Real.sqrt ((magnitude : ℝ) * (2 : ℝ)^1074) / (2 : ℝ)^1074 := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ magnitude),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ magnitude), hsqrtScale]
    field_simp
  have hvalueA : value a = (magnitude : ℝ) / (2 : ℝ)^1074 := by
    simp [value, magnitude, Wasm.IEEE64.scaledValue, hsign]
  have hvalueResult : value result =
      (Wasm.IEEE64.scaledMagnitude result : ℝ) / (2 : ℝ)^1074 := by
    simp [value, Wasm.IEEE64.scaledValue, hs.2.1, result]
  have heq : value result - Real.sqrt (value a) =
      ((Wasm.IEEE64.scaledMagnitude result : ℝ) -
        Real.sqrt ((magnitude : ℝ) * (2 : ℝ)^1074)) / (2 : ℝ)^1074 := by
    rw [hvalueA, hvalueResult, hsqrtScaled]
    ring
  change |value result - Real.sqrt (value a)| ≤ unitRoundoff64 * Real.sqrt (value a)
  rw [heq, abs_div, abs_of_pos hscalePos, hvalueA, hsqrtScaled]
  have herr : |(Wasm.IEEE64.scaledMagnitude result : ℝ) -
      Real.sqrt ((magnitude : ℝ) * (2 : ℝ)^1074)| ≤
      unitRoundoff64 * Real.sqrt ((magnitude : ℝ) * (2 : ℝ)^1074) := by
    simpa only [result, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hs.2.2
  exact (div_le_div_of_nonneg_right herr hscalePos.le).trans_eq (by ring)

#print axioms sqrt_real_relative
end Project.ProofKit.F64SqrtBounds
