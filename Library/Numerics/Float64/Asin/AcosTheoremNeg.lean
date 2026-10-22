import Library.Numerics.Float64.Asin.AcosTheoremSmall

/-!
`Asin.acos x` for `-1 < x ≤ -1/2`: `π - 2 (s + (r s - pio2_lo))` with the exact
`z = (1 + x)/2 ≤ 1/4`, `s = √z`, and `r = asinRatio z`, against
`arccos x = π - 2 arcsin √z`.  The result lies in `[2π/3, π]`, where one spacing is `2 ^ -51`, and
the absolute error before the last subtraction stays below `3.1 · 2 ^ -53`.
-/

namespace Library.Numerics.Float64.Asin.AcosTheoremNeg
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest PolyBound AsinTheoremSupport
  AsinTheoremRatio AsinTheoremBranches AsinTheoremSmall AcosTheoremBranches AcosTheoremSmall

set_option exponentiation.threshold 4096

theorem pi_finite : Finite (0x400921FB54442D18 : UInt64) := by
  unfold CodeLib.IEEE64.Finite; decide +kernel

theorem pi_twice : value (0x400921FB54442D18 : UInt64) = 2 * value (0x3FF921FB54442D18 : UInt64) := by
  rw [← ratOfWord_cast, ← ratOfWord_cast,
    show ratOfWord 0x400921FB54442D18 = 2 * ratOfWord 0x3FF921FB54442D18 by decide +kernel]
  push_cast
  ring

theorem two_boundary : value (UInt64.ofNat (1024 * 2 ^ 52)) = 2 := by
  rw [F64PositiveSpacing.boundary_value 1024 (by norm_num) (by norm_num)]
  norm_num

theorem neg_within (x : Float) (hx : Finite x.toBits) (h1 : -1 < value x.toBits)
    (h2 : value x.toBits ≤ -1 / 2) :
    F64SignedRounding.WithinSteps 1 (Real.arccos (value x.toBits))
      (negTail ((1.0 + x) * 0.5)).toBits := by
  obtain ⟨hzf, hzv, hz0⟩ := neg_z_exact x hx h1 h2
  have hy := arccos_neg_half (value x.toBits) (by linarith) (by linarith)
  unfold negTail piF pio2LoF
  set v := value x.toBits with hv
  set z := (1.0 + x) * 0.5 with hzdef
  set vz := (1 + v) / 2 with hvz
  have hvzp : 0 < vz := lt_of_lt_of_le (by positivity) hz0
  have hvz4 : vz ≤ 1 / 4 := by rw [hvz]; linarith
  -- `r`
  have ht : FSApprox z vz vz 1 0 :=
    (fsapprox_input z hzf vz hvzp (by linarith) (by rw [hzv, abs_of_pos hvzp])).congr hzv
  have hr := ratio_W z vz vz (ht.mono le_rfl (by norm_num)) hvzp.le hvz4 hvz4
    (le_trans (by norm_num) hz0)
  rw [ratio_eval] at hr
  obtain ⟨hrA, hrM⟩ := Library.Numerics.Float64.Log1p.Log1pTheoremTail.fsapprox_abs hr hvz4
  set R := vz * eval AsinKernelPoly.asinP vz / eval AsinKernelPoly.asinQ vz with hR
  -- `s = √z`
  have hzA : FApprox z vz 0 := ⟨hzf, by rw [hzv, sub_self, abs_zero]⟩
  have hsq0 : 0 < Real.sqrt vz := Real.sqrt_pos.mpr hvzp
  have hsq2 : Real.sqrt vz ≤ 1 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
    linarith
  have hsq27 : 1 / 2 ^ 27 ≤ Real.sqrt vz := by
    rw [Real.le_sqrt (by positivity) hvzp.le]
    norm_num
    linarith
  have hs := Approx.mono (fapprox_sqrt hzA vz vz hvzp le_rfl hvzp le_rfl (Real.sqrt vz)
    (by rw [add_zero])) (e' := (1 / 2) / 2 ^ 53) (by
      rw [zero_div, zero_add]
      exact div_le_div_of_nonneg_right hsq2 (by positivity))
  -- `r s`
  have hrs := Approx.mono (fapprox_mul hrA hs (1621 / 5000 * (1 / 4)) (1 / 2) hrM
    (by rw [abs_of_pos hsq0]; exact hsq2)
    ((1621 / 5000 * (1 / 4) + 29019 / 10000 / 2 ^ 53 * (1 / 4)) * (1 / 2 + (1 / 2) / 2 ^ 53))
    le_rfl (by norm_num)) (e' := (45 / 100) / 2 ^ 53) (by norm_num)
  have hRs : |R * Real.sqrt vz| ≤ 1621 / 5000 * (1 / 4) * (1 / 2) := by
    rw [abs_mul, abs_of_pos hsq0]
    exact mul_le_mul hrM hsq2 hsq0.le (by norm_num)
  -- `w = r s - pio2_lo`
  have hlo := lo_bound
  have hw := fapprox_sub hrs (fapprox_ofBits _ lo_finite) (41 / 1000) (by
    have h3 := abs_sub (R * Real.sqrt vz) (value 0x3C91A62633145C07)
    have h4 : (1621 / 5000 * (1 / 4) * (1 / 2) : ℝ) + 1 / 10 ^ 16 + ((45 / 100) / 2 ^ 53 + 0) ≤
        41 / 1000 := by norm_num
    linarith) (by norm_num)
  have hwv : |R * Real.sqrt vz - value 0x3C91A62633145C07| ≤ 1621 / 5000 * (1 / 4) * (1 / 2) +
      1 / 10 ^ 16 := by
    have h3 := abs_sub (R * Real.sqrt vz) (value 0x3C91A62633145C07)
    linarith
  -- `s + w`
  have hsw := Approx.mono (fapprox_add hs hw (55 / 100) (by
    have h3 := abs_add_le (Real.sqrt vz) (R * Real.sqrt vz - value 0x3C91A62633145C07)
    rw [abs_of_pos hsq0] at h3
    have h4 : (1 / 2 : ℝ) + (1621 / 5000 * (1 / 4) * (1 / 2) + 1 / 10 ^ 16) +
        ((1 / 2) / 2 ^ 53 + (45 / 100 / 2 ^ 53 + 0 + 41 / 1000 / 2 ^ 53)) ≤ 55 / 100 := by
      norm_num
    linarith) (by norm_num)) (e' := (155 / 100) / 2 ^ 53) (by norm_num)
  -- `2 (s + w)` is exact
  set sw := z.sqrt + (Asin.asinRatio z * z.sqrt - Float.ofBits 0x3C91A62633145C07) with hswd
  have hlow : 1 / 2 ^ 28 ≤ Real.sqrt vz + (R * Real.sqrt vz - value 0x3C91A62633145C07) := by
    have h3 : R * Real.sqrt vz ≥ -(1621 / 5000 * (1 / 4)) * Real.sqrt vz := by
      have := (abs_le.mp hrM).1
      nlinarith
    have h4 : (1 : ℝ) / 2 ^ 28 + 1 / 10 ^ 16 ≤ (1 - 1621 / 5000 * (1 / 4)) * (1 / 2 ^ 27) := by
      norm_num
    have h5 := (abs_le.mp hlo).2
    nlinarith
  have hsw1 : 1 / 2 ^ 1000 ≤ |value sw.toBits| := by
    have h3 := hsw.lower
    have h4 : (1 : ℝ) / 2 ^ 1000 + (155 / 100) / 2 ^ 53 ≤ 1 / 2 ^ 28 := by norm_num
    rw [abs_of_pos (by linarith)]
    linarith
  have hsw2 : |value sw.toBits| < 2 ^ 900 := by
    have h3 := hsw.mag
    have h4 := abs_add_le (Real.sqrt vz) (R * Real.sqrt vz - value 0x3C91A62633145C07)
    rw [abs_of_pos hsq0] at h4
    have h5 : (1 / 2 : ℝ) + (1621 / 5000 * (1 / 4) * (1 / 2) + 1 / 10 ^ 16) + 1 < 2 ^ 900 := by
      norm_num
    have h6 : (155 / 100 : ℝ) / 2 ^ 53 ≤ 1 := by norm_num
    linarith
  obtain ⟨h2f, h2v⟩ := Library.Numerics.Float64.Atan.AtanTheoremReduce.double_float sw hsw.1 hsw1 hsw2
  have htwo : FApprox (2.0 * sw)
      (2 * (Real.sqrt vz + (R * Real.sqrt vz - value 0x3C91A62633145C07)))
        (2 * ((155 / 100) / 2 ^ 53)) := by
    refine ⟨h2f, ?_⟩
    rw [h2v, show 2 * value sw.toBits - 2 * (Real.sqrt vz + (R * Real.sqrt vz -
      value 0x3C91A62633145C07)) = 2 * (value sw.toBits - (Real.sqrt vz + (R * Real.sqrt vz -
        value 0x3C91A62633145C07))) by ring, abs_mul, abs_two]
    have := hsw.2
    linarith
  -- the exact value against `arccos x`
  have hpi := Library.Numerics.Float64.Atan.AtanTheoremConst.atan_inf
  have hker := asin_kernel (Real.sqrt vz) (by rw [abs_of_pos hsq0]; exact hsq2)
  rw [Real.mul_self_sqrt hvzp.le, abs_of_pos hsq0, ← hR] at hker
  have hk3 : Real.sqrt vz ^ 3 * ((11 / 16) / 2 ^ 56) ≤ (1 / 2) ^ 3 * ((11 / 16) / 2 ^ 56) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hsq0.le hsq2 3) (by positivity)
  have hd : |value 0x400921FB54442D18 - 2 * (Real.sqrt vz + (R * Real.sqrt vz -
      value 0x3C91A62633145C07)) - Real.arccos v| ≤
        2 / 2 ^ 64 + 2 * ((1 / 2) ^ 3 * ((11 / 16) / 2 ^ 56)) := by
    rw [hy, pi_twice, show 2 * value 0x3FF921FB54442D18 - 2 * (Real.sqrt vz +
      (R * Real.sqrt vz - value 0x3C91A62633145C07)) -
        (Real.pi - 2 * Real.arcsin (Real.sqrt vz)) =
      2 * (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2) +
        2 * (Real.arcsin (Real.sqrt vz) - (Real.sqrt vz + Real.sqrt vz * R)) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_two]
    linarith
  -- `arccos x ≥ 2π/3`
  have hs6 : Real.arcsin (Real.sqrt vz) ≤ Real.pi / 6 := by
    have hs : Real.arcsin (1 / 2) = Real.pi / 6 := by
      rw [← Real.sin_pi_div_six, Real.arcsin_sin (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])]
    rw [← hs]
    exact Real.arcsin_le_arcsin hsq2
  have hp := Real.pi_gt_d2
  have hp4 := Real.pi_lt_four
  have hpos := Real.arcsin_nonneg.mpr hsq0.le
  refine sub_within (fapprox_ofBits _ pi_finite) htwo (Real.arccos v) ((7 / 2) / 2 ^ 53) ?_ 1024
    (by norm_num) (by norm_num) ?_ (by norm_num) ?_
  · have h3 : (0 : ℝ) + 2 * ((155 / 100) / 2 ^ 53) + (2 / 2 ^ 64 +
        2 * ((1 / 2) ^ 3 * ((11 / 16) / 2 ^ 56))) ≤ (7 / 2) / 2 ^ 53 := by norm_num
    linarith
  · rw [two_boundary, hy, abs_of_pos (by linarith)]
    have h3 : (2 : ℝ) + (7 / 2) / 2 ^ 53 ≤ 314 / 100 - 2 * (314 / 100 / 6) := by norm_num
    linarith
  · rw [hy, abs_lt]
    have h3 : (4 : ℝ) < 2 ^ 1022 := by norm_num
    constructor <;> linarith

#print axioms neg_within

end Library.Numerics.Float64.Asin.AcosTheoremNeg
