import Project.ExpSmall.Model
import Project.ExpSmall.Real
import Project.ProofKit.F64Horner

namespace Project.ExpSmall
open CodeLib.IEEE64 Project.ProofKit.F64Horner

set_option exponentiation.threshold 4096

private theorem coefficient6 : Approximation 0x3F56C16C16C16C17 (1 / 720) 1 arithmeticEpsilon := by
  constructor
  · unfold CodeLib.IEEE64.Finite; decide
  all_goals norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]

private theorem coefficient5 : Approximation 0x3F81111111111111 (1 / 120) 1 arithmeticEpsilon := by
  constructor
  · unfold CodeLib.IEEE64.Finite; decide
  all_goals norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]

private theorem coefficient4 : Approximation 0x3FA5555555555555 (1 / 24) 1 arithmeticEpsilon := by
  constructor
  · unfold CodeLib.IEEE64.Finite; decide
  all_goals norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]

private theorem coefficient3 : Approximation 0x3FC5555555555555 (1 / 6) 1 arithmeticEpsilon := by
  constructor
  · unfold CodeLib.IEEE64.Finite; decide
  all_goals norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]

private theorem coefficient2 : Approximation 0x3FE0000000000000 (1 / 2) 1 arithmeticEpsilon := by
  constructor
  · unfold CodeLib.IEEE64.Finite; decide
  all_goals norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]

private theorem coefficient1 : Approximation 0x3FF0000000000000 1 1 arithmeticEpsilon := by
  constructor
  · unfold CodeLib.IEEE64.Finite; decide
  all_goals norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]

theorem polynomial_roundoff (x : UInt64) (hx : Finite x) (bx : |value x| ≤ 1) :
    Finite (polynomial x) ∧
      |value (polynomial x) - polynomialReal (value x)| ≤ 211 * arithmeticEpsilon := by
  have h5 := step coefficient6 coefficient5 hx bx (by norm_num)
  have h4 := step h5 coefficient4 hx bx (by norm_num)
  have h3 := step h4 coefficient3 hx bx (by norm_num)
  have h2 := step h3 coefficient2 hx bx (by norm_num)
  have h1 := step h2 coefficient1 hx bx (by norm_num)
  have h0 := step h1 coefficient1 hx bx (by norm_num)
  refine ⟨h0.finite, ?_⟩
  convert h0.accuracy using 1 <;> (try dsimp only [polynomial, polynomialReal]) <;> ring

theorem polynomial_error (x : UInt64) (hx : Finite x) (bx : |value x| ≤ 1) :
    Finite (polynomial x) ∧
      |value (polynomial x) - Real.exp (value x)| ≤ 1 / 4000 := by
  have h := polynomial_roundoff x hx bx
  refine ⟨h.1, ?_⟩
  calc
    _ ≤ |value (polynomial x) - polynomialReal (value x)| +
        |polynomialReal (value x) - Real.exp (value x)| := abs_sub_le _ _ _
    _ ≤ 211 * arithmeticEpsilon + 1 / 4410 :=
      add_le_add h.2 (polynomialReal_error _ bx)
    _ ≤ 1 / 4000 := by norm_num [arithmeticEpsilon]

theorem exp_negative_unit_bounds (x : ℝ) (hl : -1 ≤ x) (hu : x ≤ 0) :
    1 / 3 ≤ Real.exp x ∧ Real.exp x ≤ 1 := by
  have h := Real.exp_bound' (x := 1) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hm : Real.exp (-x) ≤ 3 :=
    (Real.exp_le_exp.mpr (show -x ≤ 1 by linarith)).trans (by linarith)
  have hi : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hp := mul_le_mul_of_nonneg_left hm (Real.exp_pos x).le
  exact ⟨by nlinarith, by simpa using Real.exp_le_exp.mpr hu⟩

theorem polynomial_positive (x : UInt64) (hx : Finite x)
    (hl : -1 ≤ value x) (hu : value x ≤ 0) :
    Finite (polynomial x) ∧ 0 < value (polynomial x) ∧
      value (polynomial x) ≤ 1 + 1 / 4000 ∧
      |value (polynomial x) - Real.exp (value x)| ≤ 1 / 4000 := by
  have bx : |value x| ≤ 1 := abs_le.mpr ⟨hl, by linarith⟩
  have h := polynomial_error x hx bx
  have he := exp_negative_unit_bounds (value x) hl hu
  have ha := abs_le.mp h.2
  exact ⟨h.1, by linarith, by linarith, h.2⟩

#print axioms polynomial_roundoff
#print axioms polynomial_error
#print axioms polynomial_positive
end Project.ExpSmall
