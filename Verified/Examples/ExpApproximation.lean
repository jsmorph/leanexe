import CodeLib.IEEE64.Roundoff
import LeanExe.ProofKit.RealExpError

namespace Verified.Examples.ExpApproximation
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

noncomputable def polynomial (r : ℝ) : ℝ :=
  r + r ^ 2 * (value 0x3FDFFFFFFFFFFDBD + r * value 0x3FC555555555543C) +
    r ^ 4 * (value 0x3FA55555CF172B91 + r * value 0x3F81111167A4D017)

theorem coefficient_values :
    value 0x3FDFFFFFFFFFFDBD = 9007199254740413 / (2 : ℝ) ^ 54 ∧
    value 0x3FC555555555543C = 6004799503160380 / (2 : ℝ) ^ 55 ∧
    value 0x3FA55555CF172B91 = 6004801545907089 / (2 : ℝ) ^ 57 ∧
    value 0x3F81111167A4D017 = 4803841055051799 / (2 : ℝ) ^ 59 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem coefficient_error (r : ℝ) (hr : |r| ≤ 1 / 256) :
    |(1 + polynomial r) -
      (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120)| ≤
      5 / (2 : ℝ) ^ 60 := by
  let d2 := value 0x3FDFFFFFFFFFFDBD - (1 / 2 : ℝ)
  let d3 := value 0x3FC555555555543C - (1 / 6 : ℝ)
  let d4 := value 0x3FA55555CF172B91 - (1 / 24 : ℝ)
  let d5 := value 0x3F81111167A4D017 - (1 / 120 : ℝ)
  have hd :
      (1 + polynomial r) -
        (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120) =
        d2 * r ^ 2 + d3 * r ^ 3 + d4 * r ^ 4 + d5 * r ^ 5 := by
    dsimp [polynomial, d2, d3, d4, d5]
    ring
  rw [hd]
  calc
    _ ≤ |d2 * r ^ 2| + |d3 * r ^ 3| + |d4 * r ^ 4| + |d5 * r ^ 5| := by
      have h23 := abs_add_le (d2 * r ^ 2) (d3 * r ^ 3)
      have h234 := (abs_add_le (d2 * r ^ 2 + d3 * r ^ 3) (d4 * r ^ 4)).trans
        (add_le_add h23 le_rfl)
      exact (abs_add_le (d2 * r ^ 2 + d3 * r ^ 3 + d4 * r ^ 4)
        (d5 * r ^ 5)).trans (add_le_add h234 le_rfl)
    _ = |d2| * |r| ^ 2 + |d3| * |r| ^ 3 + |d4| * |r| ^ 4 + |d5| * |r| ^ 5 := by
      simp only [abs_mul, abs_pow]
    _ ≤ |d2| * (1 / 256 : ℝ) ^ 2 + |d3| * (1 / 256 : ℝ) ^ 3 +
        |d4| * (1 / 256 : ℝ) ^ 4 + |d5| * (1 / 256 : ℝ) ^ 5 := by
      gcongr
    _ ≤ 5 / (2 : ℝ) ^ 60 := by
      obtain ⟨h2, h3, h4, h5⟩ := coefficient_values
      dsimp [d2, d3, d4, d5]
      rw [h2, h3, h4, h5]
      norm_num

theorem polynomial_error (r : ℝ) (hr : |r| ≤ 1 / 256) :
    |Real.exp r - (1 + polynomial r)| ≤ 1 / (2 : ℝ) ^ 56 := by
  let t := 1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120
  have ht : |Real.exp r - t| ≤ 7 / (2 : ℝ) ^ 60 :=
    LeanExe.ProofKit.RealExpError.taylor_five_error_small r hr
  have hc : |t - (1 + polynomial r)| ≤ 5 / (2 : ℝ) ^ 60 := by
    rw [abs_sub_comm]
    exact coefficient_error r hr
  calc
    _ ≤ |Real.exp r - t| + |t - (1 + polynomial r)| := abs_sub_le _ _ _
    _ ≤ 7 / (2 : ℝ) ^ 60 + 5 / (2 : ℝ) ^ 60 := add_le_add ht hc
    _ ≤ 1 / (2 : ℝ) ^ 56 := by norm_num

#print axioms coefficient_values
#print axioms coefficient_error
#print axioms polynomial_error

end Verified.Examples.ExpApproximation
