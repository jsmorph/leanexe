import Library.Numerics.Float64.Tgamma.TgammaDD

/-!
The two polynomials of `Tgamma.asSinpid` in `d2 = d * d`, for `|d| ≤ 1/2`.  The code evaluates
`p = d2 (c131 + d2 (c132 + d2 c133))` for the cosine kernel and `q = d2 (c135 + d2 (c136 + d2 c137))`
for the sine kernel with rounded operations.  `d2_spec` bounds `d2 - d²` by `2^-55 + 2^-1075`,
`p_spec` bounds `p` within `2^-77` of the same expression in `d²` with exact operations, and
`q_spec` bounds `q` within `2.1 · 10^-22` of it, for the coefficient bounds of the code's table.
Each step follows the rounded operations through `F64Approx`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaSinpidPoly
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx TgammaDD

set_option exponentiation.threshold 4096

theorem d2_spec (d : Float) (hd : Finite d.toBits) (hD : |value d.toBits| ≤ 1 / 2) :
    FApprox (d * d) (value d.toBits ^ 2) (1 / 2 ^ 55 + 1 / 2 ^ 1075) := by
  have h := fapprox_mul (fapprox_self d hd) (fapprox_self d hd) (1 / 2) (1 / 2) hD hD (1 / 4)
    (by norm_num) (by norm_num)
  rw [← sq] at h
  exact h.mono (le_of_eq (by norm_num))

theorem sq_le (D : ℝ) (hD : |D| ≤ 1 / 2) : |D ^ 2| ≤ 1 / 4 := by
  rw [abs_pow]
  calc |D| ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg D) hD 2
    _ = 1 / 4 := by norm_num

/-- `|a + D² b| ≤ A + B/4` for `|a| ≤ A`, `|b| ≤ B`, `|D| ≤ 1/2`. -/
theorem add_sq_le (D a b A B : ℝ) (hD : |D| ≤ 1 / 2) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a + D ^ 2 * b| ≤ A + B / 4 := by
  have h1 := abs_add_le a (D ^ 2 * b)
  have h2 : |D ^ 2 * b| ≤ 1 / 4 * B := by
    rw [abs_mul]
    exact mul_le_mul (sq_le D hD) hb (abs_nonneg _) (by norm_num)
  linarith

theorem sq_mul_le (D b B : ℝ) (hD : |D| ≤ 1 / 2) (hb : |b| ≤ B) : |D ^ 2 * b| ≤ B / 4 := by
  rw [abs_mul]
  have := mul_le_mul (sq_le D hD) hb (abs_nonneg _) (by norm_num)
  linarith

/-- **The cosine polynomial** `p`, within `2^-77`. -/
theorem p_spec (d c131 c132 c133 : Float) (hd : Finite d.toBits) (h131 : Finite c131.toBits)
    (h132 : Finite c132.toBits) (h133 : Finite c133.toBits) (hD : |value d.toBits| ≤ 1 / 2)
    (hb131 : |value c131.toBits| ≤ 1 / 2 ^ 25) (hb132 : |value c132.toBits| ≤ 1 / 2 ^ 41)
    (hb133 : |value c133.toBits| ≤ 1 / 2 ^ 58) :
    FApprox ((d * d) * (c131 + (d * d) * (c132 + (d * d) * c133)))
      (value d.toBits ^ 2 * (value c131.toBits + value d.toBits ^ 2 *
        (value c132.toBits + value d.toBits ^ 2 * value c133.toBits))) (1 / 2 ^ 77) := by
  set D := value d.toBits
  have hU := d2_spec d hd hD
  have hD2 := sq_le D hD
  have h1 := (fapprox_mul hU (fapprox_self c133 h133) (1 / 4) (1 / 2 ^ 58) hD2 hb133 (1 / 2 ^ 59)
    (by norm_num) (by norm_num)).mono (show _ ≤ (1 / 2 ^ 111 : ℝ) by norm_num)
  have hm1 := sq_mul_le D _ _ hD hb133
  have h2 := (fapprox_add (fapprox_self c132 h132) h1 (1 / 2 ^ 40) (by
    have := add_sq_le D _ _ _ _ hD hb132 hb133
    linarith [(by norm_num : (1 / 2 ^ 41 + 1 / 2 ^ 58 / 4 : ℝ) + (0 + 1 / 2 ^ 111) ≤ 1 / 2 ^ 40)])
    (by norm_num)).mono (show _ ≤ (1 / 2 ^ 92 : ℝ) by norm_num)
  have hb2 := add_sq_le D _ _ _ _ hD hb132 hb133
  have h3 := (fapprox_mul hU h2 (1 / 4) (1 / 2 ^ 41 + 1 / 2 ^ 58 / 4) hD2 hb2 (1 / 2 ^ 42)
    (by norm_num) (by norm_num)).mono (show _ ≤ (1 / 2 ^ 93 : ℝ) by norm_num)
  have hb3 := add_sq_le D _ _ _ _ hD hb131 hb2
  have h4 := (fapprox_add (fapprox_self c131 h131) h3 (1 / 2 ^ 24) (by
    linarith [(by norm_num : (1 / 2 ^ 25 + (1 / 2 ^ 41 + 1 / 2 ^ 58 / 4) / 4 : ℝ) +
      (0 + 1 / 2 ^ 93) ≤ 1 / 2 ^ 24)])
    (by norm_num)).mono (show _ ≤ (1 / 2 ^ 76 : ℝ) by norm_num)
  exact (fapprox_mul hU h4 (1 / 4) (1 / 2 ^ 25 + (1 / 2 ^ 41 + 1 / 2 ^ 58 / 4) / 4) hD2 hb3
    (1 / 2 ^ 26) (by norm_num) (by norm_num)).mono (by norm_num)

/-- **The sine polynomial** `q`, within `2.1 · 10^-22`. -/
theorem q_spec (d c135 c136 c137 : Float) (hd : Finite d.toBits) (h135 : Finite c135.toBits)
    (h136 : Finite c136.toBits) (h137 : Finite c137.toBits) (hD : |value d.toBits| ≤ 1 / 2)
    (hb135 : |value c135.toBits| ≤ 2465 / 10 ^ 9) (hb136 : |value c136.toBits| ≤ 1 / 2 ^ 33)
    (hb137 : |value c137.toBits| ≤ 1 / 2 ^ 49) :
    FApprox ((d * d) * (c135 + (d * d) * (c136 + (d * d) * c137)))
      (value d.toBits ^ 2 * (value c135.toBits + value d.toBits ^ 2 *
        (value c136.toBits + value d.toBits ^ 2 * value c137.toBits))) (21 / 10 ^ 23) := by
  set D := value d.toBits
  have hU := d2_spec d hd hD
  have hD2 := sq_le D hD
  have h1 := (fapprox_mul hU (fapprox_self c137 h137) (1 / 4) (1 / 2 ^ 49) hD2 hb137 (1 / 2 ^ 50)
    (by norm_num) (by norm_num)).mono (show _ ≤ (1 / 2 ^ 102 : ℝ) by norm_num)
  have hb2 := add_sq_le D _ _ _ _ hD hb136 hb137
  have h2 := (fapprox_add (fapprox_self c136 h136) h1 (1 / 2 ^ 32) (by
    linarith [(by norm_num : (1 / 2 ^ 33 + 1 / 2 ^ 49 / 4 : ℝ) + (0 + 1 / 2 ^ 102) ≤ 1 / 2 ^ 32)])
    (by norm_num)).mono (show _ ≤ (1 / 2 ^ 84 : ℝ) by norm_num)
  have h3 := (fapprox_mul hU h2 (1 / 4) (1 / 2 ^ 33 + 1 / 2 ^ 49 / 4) hD2 hb2 (1 / 2 ^ 34)
    (by norm_num) (by norm_num)).mono (show _ ≤ (1 / 2 ^ 85 : ℝ) by norm_num)
  have hb3 := add_sq_le D _ _ _ _ hD hb135 hb2
  have h4 := (fapprox_add (fapprox_self c135 h135) h3 (2466 / 10 ^ 9) (by
    linarith [(by norm_num : (2465 / 10 ^ 9 + (1 / 2 ^ 33 + 1 / 2 ^ 49 / 4) / 4 : ℝ) +
      (0 + 1 / 2 ^ 85) ≤ 2466 / 10 ^ 9)])
    (by norm_num)).mono (show _ ≤ (274 / 10 ^ 24 : ℝ) by norm_num)
  have hb4 : |value c135.toBits + D ^ 2 * (value c136.toBits + D ^ 2 * value c137.toBits)| ≤
      2466 / 10 ^ 9 := by
    linarith [(by norm_num : (2465 / 10 ^ 9 + (1 / 2 ^ 33 + 1 / 2 ^ 49 / 4) / 4 : ℝ) ≤
      2466 / 10 ^ 9)]
  exact (fapprox_mul hU h4 (1 / 4) (2466 / 10 ^ 9) hD2 hb4 (6166 / 10 ^ 10) (by norm_num)
    (by norm_num)).mono (by norm_num)

#print axioms p_spec
#print axioms q_spec

end Library.Numerics.Float64.Tgamma.TgammaSinpidPoly
