import Library.Numerics.Float64.Tgamma.TgammaRefl4

/-!
The quotient `rh + rl` of the path of `tgammaWith` below `-3` against `T = π P/(s Γ1)`, where
`s = sin (π d)`, `Γ1 = Γ (1 - x)`, and `P = 2 ^ E`.  `prod_close` puts the product
`(ph + pl) P` of `asSinpid` and `asExpd` within `10 · 2 ^ -60` of `s Γ1` relative, and
`refl_real` puts `rh + rl` within `11 · 2 ^ -60` of `T` relative and `rh` alone within
`24 · 2 ^ -53`, from the low part `|pl| ≤ 18.01 · 2 ^ -53 ph` and the bound `2 ^ -49/ph` of `rh`
against `p1/ph`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaRefl5
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaRefl4

set_option exponentiation.threshold 4096

/-- **The product** `(ph + pl) P` against `s Γ1`. -/
theorem prod_close (Γ1 s P vh vl vsh vsl vph vpl : ℝ) (hΓ : 0 < Γ1) (hs : 0 < s) (hP : 0 < P)
    (hQ : |(vh + vl) * P - Γ1| ≤ 5 * Γ1 / 2 ^ 60) (hh1 : 1 / 2 ≤ vh) (hl : |vl| ≤ vh / 2 ^ 50)
    (hsh : 0 < vsh) (hS : |vsh + vsl - s| ≤ s / 2 ^ 58) (hsl : |vsl| ≤ vsh / 2 ^ 50)
    (hD : |vph + vpl - (vsh + vsl) * (vh + vl)| ≤ vh * vsh / 2 ^ 97) :
    |(vph + vpl) * P - s * Γ1| ≤ 10 / 2 ^ 60 * (s * Γ1) := by
  have hSv : vsh * (1 - 1 / 2 ^ 50) ≤ vsh + vsl := by linarith [(abs_le.mp hsl).1]
  have hHv : vh * (1 - 1 / 2 ^ 50) ≤ vh + vl := by linarith [(abs_le.mp hl).1]
  have hSvs : vsh + vsl ≤ s * (1 + 1 / 2 ^ 58) := by linarith [(abs_le.mp hS).2]
  have hQup : (vh + vl) * P ≤ Γ1 * (1 + 5 / 2 ^ 60) := by linarith [(abs_le.mp hQ).2]
  have hQ0 : 0 ≤ (vh + vl) * P := mul_nonneg (by linarith) hP.le
  have hK : 0 < s * Γ1 := mul_pos hs hΓ
  -- `vh vsh P ≤ 2 s Γ1`
  have e1 : vh * (1 - 1 / 2 ^ 50) * (vsh * (1 - 1 / 2 ^ 50)) ≤ (vh + vl) * (vsh + vsl) :=
    mul_le_mul hHv hSv (by nlinarith) (by linarith)
  have e2 : (vsh + vsl) * ((vh + vl) * P) ≤ s * (1 + 1 / 2 ^ 58) * (Γ1 * (1 + 5 / 2 ^ 60)) :=
    mul_le_mul hSvs hQup hQ0 (by positivity)
  have e3 : vh * vsh * P ≤ 2 * (s * Γ1) := by
    have h1 := mul_le_mul_of_nonneg_right e1 hP.le
    have h2 : vh * (1 - 1 / 2 ^ 50) * (vsh * (1 - 1 / 2 ^ 50)) * P =
        (vh * vsh * P) * ((1 - 1 / 2 ^ 50) * (1 - 1 / 2 ^ 50)) := by ring
    have h3 : (vh + vl) * (vsh + vsl) * P = (vsh + vsl) * ((vh + vl) * P) := by ring
    rw [h2, h3] at h1
    have h4 : s * (1 + 1 / 2 ^ 58) * (Γ1 * (1 + 5 / 2 ^ 60)) =
        (s * Γ1) * ((1 + 1 / 2 ^ 58) * (1 + 5 / 2 ^ 60)) := by ring
    rw [h4] at e2
    linarith
  -- the two parts
  have t1 : |(vph + vpl - (vsh + vsl) * (vh + vl)) * P| ≤ 2 * (s * Γ1) / 2 ^ 97 := by
    rw [abs_mul, abs_of_pos hP]
    calc |vph + vpl - (vsh + vsl) * (vh + vl)| * P ≤ vh * vsh / 2 ^ 97 * P :=
          mul_le_mul_of_nonneg_right hD hP.le
      _ = vh * vsh * P / 2 ^ 97 := by ring
      _ ≤ 2 * (s * Γ1) / 2 ^ 97 := div_le_div_of_nonneg_right e3 (by norm_num)
  have t2 : |(vsh + vsl) * ((vh + vl) * P - Γ1)| ≤ s * (1 + 1 / 2 ^ 58) * (5 * Γ1 / 2 ^ 60) := by
    rw [abs_mul, abs_of_pos (by nlinarith : (0 : ℝ) < vsh + vsl)]
    exact mul_le_mul hSvs hQ (abs_nonneg _) (by positivity)
  have t3 : |(vsh + vsl - s) * Γ1| ≤ s / 2 ^ 58 * Γ1 := by
    rw [abs_mul, abs_of_pos hΓ]
    exact mul_le_mul_of_nonneg_right hS hΓ.le
  have hsplit : (vph + vpl) * P - s * Γ1 = (vph + vpl - (vsh + vsl) * (vh + vl)) * P +
      (vsh + vsl) * ((vh + vl) * P - Γ1) + (vsh + vsl - s) * Γ1 := by ring
  rw [hsplit]
  have a1 := abs_add_le ((vph + vpl - (vsh + vsl) * (vh + vl)) * P +
    (vsh + vsl) * ((vh + vl) * P - Γ1)) ((vsh + vsl - s) * Γ1)
  have a2 := abs_add_le ((vph + vpl - (vsh + vsl) * (vh + vl)) * P)
    ((vsh + vsl) * ((vh + vl) * P - Γ1))
  have : s * (1 + 1 / 2 ^ 58) * (5 * Γ1 / 2 ^ 60) = (s * Γ1) * ((1 + 1 / 2 ^ 58) * 5 / 2 ^ 60) := by
    ring
  have : s / 2 ^ 58 * Γ1 = (s * Γ1) / 2 ^ 58 := by ring
  linarith

/-- **The quotient** `rh + rl` against `T = π P/(s Γ1)`, and `rh` alone. -/
theorem refl_real (Γ1 s P vph vpl vp1 vp2 vrh vrl : ℝ) (hΓ : 0 < Γ1) (hs : 0 < s) (hP : 0 < P)
    (hZ : |(vph + vpl) * P - s * Γ1| ≤ 10 / 2 ^ 60 * (s * Γ1))
    (hph : 0 < vph) (hpl : |vpl| ≤ vph * (1801 / 100 / 2 ^ 53))
    (hp1a : 3141592 / 10 ^ 6 ≤ vp1)
    (hp2 : |vp2| ≤ 1104 / 1000 / 2 ^ 53) (hPc : |vp1 + vp2 - Real.pi| ≤ 1 / 10 ^ 20)
    (hrh : |vrh - vp1 / vph| ≤ 1 / vph / 2 ^ 49)
    (hR : |vrh + vrl - (vp1 + vp2) / (vph + vpl)| ≤ |(vp1 + vp2) / (vph + vpl)| / 2 ^ 68) :
    |vrh + vrl - Real.pi * P / (s * Γ1)| ≤ 11 * (Real.pi * P / (s * Γ1)) / 2 ^ 60 ∧
      |vrh - Real.pi * P / (s * Γ1)| ≤ 24 * (Real.pi * P / (s * Γ1)) / 2 ^ 53 := by
  have hK : 0 < s * Γ1 := mul_pos hs hΓ
  have hpl' : vph * (1 - 1801 / 100 / 2 ^ 53) ≤ vph + vpl := by linarith [(abs_le.mp hpl).1]
  have hD : 0 < vph + vpl := lt_of_lt_of_le (by positivity) hpl'
  have hDne := hD.ne'
  have hPne := hP.ne'
  have hphne := hph.ne'
  have hpi := Real.pi_pos
  obtain ⟨T, hT⟩ : ∃ T, T = Real.pi * P / (s * Γ1) := ⟨_, rfl⟩
  rw [← hT]
  have hT0 : 0 < T := by rw [hT]; positivity
  -- `Pc/D` against `T`
  have hr := ratio_err (s * Γ1) ((vph + vpl) * P) (vp1 + vp2) (10 / 2 ^ 60) (1 / 10 ^ 20) hK
    (by positivity) (by norm_num) hZ (by positivity) hPc
  have hc : (1 / 10 ^ 20 / 3 + 10 / 2 ^ 60) * (1 + 2 * (10 / 2 ^ 60)) ≤ (1001 / 100 : ℝ) / 2 ^ 60 := by
    norm_num
  have hPD : (vp1 + vp2) / (vph + vpl) = (vp1 + vp2) / ((vph + vpl) * P) * P := by
    field_simp
  have hTK : T = Real.pi / (s * Γ1) * P := by rw [hT]; ring
  have hq : |(vp1 + vp2) / (vph + vpl) - T| ≤ T * (1001 / 100 / 2 ^ 60) := by
    rw [hPD, hTK, ← sub_mul, abs_mul, abs_of_pos hP]
    calc |(vp1 + vp2) / ((vph + vpl) * P) - Real.pi / (s * Γ1)| * P ≤
        Real.pi / (s * Γ1) * ((1 / 10 ^ 20 / 3 + 10 / 2 ^ 60) * (1 + 2 * (10 / 2 ^ 60))) * P :=
          mul_le_mul_of_nonneg_right hr hP.le
      _ ≤ Real.pi / (s * Γ1) * (1001 / 100 / 2 ^ 60) * P := by gcongr
      _ = Real.pi / (s * Γ1) * P * (1001 / 100 / 2 ^ 60) := by ring
  obtain ⟨J, hJ⟩ : ∃ J, J = 1 / (vph + vpl) := ⟨_, rfl⟩
  have hJ0 : 0 < J := by rw [hJ]; positivity
  have hPJ : (vp1 + vp2) / (vph + vpl) = (vp1 + vp2) * J := by rw [hJ]; ring
  rw [hPJ] at hq hR
  have hPc0 : 0 < vp1 + vp2 := by linarith [(abs_le.mp hp2).1]
  rw [abs_of_pos (mul_pos hPc0 hJ0)] at hR
  have hPJT : (vp1 + vp2) * J ≤ T * (1 + 1001 / 100 / 2 ^ 60) := by linarith [(abs_le.mp hq).2]
  constructor
  · have := abs_sub_le (vrh + vrl) ((vp1 + vp2) * J) T
    linarith
  · -- `p1/ph` against `Pc/D`
    have hid : vp1 / vph - (vp1 + vp2) * J = (vp1 * (vpl / vph) - vp2) * J := by
      rw [hJ]; field_simp; ring
    have hlr : |vpl / vph| ≤ 1801 / 100 / 2 ^ 53 := by
      rw [abs_div, abs_of_pos hph, div_le_iff₀ hph]; linarith
    have hm1 : |vp1 * (vpl / vph) - vp2| ≤ vp1 * (1801 / 100 / 2 ^ 53) + 1104 / 1000 / 2 ^ 53 := by
      have := abs_sub (vp1 * (vpl / vph)) vp2
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < vp1)] at this
      have := mul_le_mul_of_nonneg_left hlr (by linarith : (0 : ℝ) ≤ vp1)
      linarith
    have hm2 : |vp1 / vph - (vp1 + vp2) * J| ≤
        (vp1 * (1801 / 100 / 2 ^ 53) + 1104 / 1000 / 2 ^ 53) * J := by
      rw [hid, abs_mul, abs_of_pos hJ0]
      exact mul_le_mul_of_nonneg_right hm1 hJ0.le
    have hm3 : (vp1 * (1801 / 100 / 2 ^ 53) + 1104 / 1000 / 2 ^ 53) * J ≤
        1837 / 100 / 2 ^ 53 * ((vp1 + vp2) * J) := by
      have : vp1 * (1801 / 100 / 2 ^ 53) + 1104 / 1000 / 2 ^ 53 ≤
          1837 / 100 / 2 ^ 53 * (vp1 + vp2) := by linarith [(abs_le.mp hp2).1]
      have := mul_le_mul_of_nonneg_right this hJ0.le
      linarith
    -- `rh` against `p1/ph`
    have hI : 1 / vph ≤ (1 + 1802 / 100 / 2 ^ 53) * J := by
      rw [hJ, div_le_iff₀ hph]
      have h1 : vph + vpl ≤ vph * (1 + 1801 / 100 / 2 ^ 53) := by linarith [(abs_le.mp hpl).2]
      rw [show (1 + 1802 / 100 / 2 ^ 53) * (1 / (vph + vpl)) * vph =
        (1 + 1802 / 100 / 2 ^ 53) * vph / (vph + vpl) by ring, le_div_iff₀ hD]
      linarith
    have hm4 : 1 / vph / 2 ^ 49 ≤ 50931 / 10000 / 2 ^ 53 * ((vp1 + vp2) * J) := by
      have h1 : 1 / vph / 2 ^ 49 ≤ (1 + 1802 / 100 / 2 ^ 53) * J / 2 ^ 49 :=
        div_le_div_of_nonneg_right hI (by norm_num)
      have h2 : (1 + 1802 / 100 / 2 ^ 53) / 2 ^ 49 ≤ 50931 / 10000 / 2 ^ 53 * (vp1 + vp2) := by
        have : (3141591 / 10 ^ 6 : ℝ) ≤ vp1 + vp2 := by linarith [(abs_le.mp hp2).1]
        have h3 : (1 + 1802 / 100 / 2 ^ 53 : ℝ) / 2 ^ 49 ≤ 50931 / 10000 / 2 ^ 53 * (3141591 / 10 ^ 6) := by
          norm_num
        linarith
      have := mul_le_mul_of_nonneg_right h2 hJ0.le
      have h4 : (1 + 1802 / 100 / 2 ^ 53) * J / 2 ^ 49 = (1 + 1802 / 100 / 2 ^ 53) / 2 ^ 49 * J := by
        ring
      linarith
    have := abs_sub_le vrh (vp1 / vph) ((vp1 + vp2) * J)
    have := abs_sub_le vrh ((vp1 + vp2) * J) T
    have h5 : 0 ≤ (vp1 + vp2) * J := by positivity
    linarith

#print axioms prod_close
#print axioms refl_real

end Library.Numerics.Float64.Tgamma.TgammaRefl5
