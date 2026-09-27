import Project.ExpArm.TinyBounds

namespace Project.ExpArm
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

noncomputable def idealPolynomial (r : ℝ) : ℝ :=
  1 + r + r^2 * (value 0x3FDFFFFFFFFFFDBD + r * value 0x3FC555555555543C) +
    r^4 * (value 0x3FA55555CF172B91 + r * value 0x3F81111167A4D017)

theorem coefficient_bounds :
    |value 0x3FDFFFFFFFFFFDBD - (1 : ℝ)/2| ≤ 1/30000000000000 ∧
    |value 0x3FC555555555543C - (1 : ℝ)/6| ≤ 1/100000000000000 ∧
    |value 0x3FA55555CF172B91 - (1 : ℝ)/24| ≤ 15/1000000000 ∧
    |value 0x3F81111167A4D017 - (1 : ℝ)/120| ≤ 3/1000000000 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem idealPolynomial_error (r : ℝ) (hr : |r| ≤ 3/1000) :
    |idealPolynomial r - Real.exp r| < 3/1000000000000000000 := by
  let t := 1 + r + r^2/2 + r^3/6 + r^4/24 + r^5/120
  have ht : |Real.exp r - t| ≤ |r|^6 * (7/4320) := by
    have h := Real.exp_bound (hr.trans (by norm_num)) (n := 6) (by decide)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    convert h using 1
  let a := (value 0x3FDFFFFFFFFFFDBD - (1 : ℝ)/2) * r^2
  let b := (value 0x3FC555555555543C - (1 : ℝ)/6) * r^3
  let c := (value 0x3FA55555CF172B91 - (1 : ℝ)/24) * r^4
  let d := (value 0x3F81111167A4D017 - (1 : ℝ)/120) * r^5
  have hp : |idealPolynomial r - t| ≤ |a| + |b| + |c| + |d| := by
    have he : idealPolynomial r - t = a + b + c + d := by
      dsimp [idealPolynomial, t, a, b, c, d]
      ring
    rw [he]
    calc
      _ ≤ |a + b + c| + |d| := abs_add_le _ _
      _ ≤ |a + b| + |c| + |d| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ |a| + |b| + |c| + |d| :=
        add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
  have hb : |a| + |b| + |c| + |d| ≤
      (1/30000000000000 : ℝ)*(3/1000)^2 +
      (1/100000000000000 : ℝ)*(3/1000)^3 +
      (15/1000000000 : ℝ)*(3/1000)^4 +
      (3/1000000000 : ℝ)*(3/1000)^5 := by
    dsimp [a, b, c, d]
    simp only [abs_mul, abs_pow]
    rcases coefficient_bounds with ⟨h2, h3, h4, h5⟩
    gcongr
  have ht' : |Real.exp r - t| ≤ (3/1000 : ℝ)^6 * (7/4320) := by
    refine ht.trans ?_
    gcongr
  have he := abs_add_le (idealPolynomial r - t) (t - Real.exp r)
  rw [sub_add_sub_cancel, abs_sub_comm t] at he
  calc
    _ ≤ |idealPolynomial r - t| + |Real.exp r - t| := he
    _ ≤ _ := add_le_add (hp.trans hb) ht'
    _ < 3/1000000000000000000 := by norm_num

#print axioms idealPolynomial_error
end Project.ExpArm
