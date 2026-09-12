import Project.Euler2DConservative.Guard

namespace Project.EulerRiemann.RealRusanov
open Project.Euler2DConservative.Guard (Vec4 internalEnergy pressure)

noncomputable def physicalFlux (q : Vec4) : Vec4 :=
  ![q 1, (q 1)^2 / q 0 + pressure q, q 1 * q 2 / q 0,
    (q 3 + pressure q) * (q 1 / q 0)]

noncomputable def splitState (q : Vec4) (b : ℝ) : Vec4 :=
  fun i => q i + b * physicalFlux q i

noncomputable def interfaceFlux (a : ℝ) (left right : Vec4) : Vec4 :=
  fun i => (physicalFlux left i + physicalFlux right i) / 2 -
    a * (right i - left i) / 2

noncomputable def update (ratio aLeft aRight : ℝ) (left center right : Vec4) : Vec4 :=
  fun i => center i - ratio *
    (interfaceFlux aRight center right i - interfaceFlux aLeft left center i)

noncomputable def combine (a b c : ℝ) (q r s : Vec4) : Vec4 :=
  fun i => a * q i + b * r i + c * s i

theorem update_decomposition (ratio aLeft aRight : ℝ) (left center right : Vec4)
    (hLeft : aLeft ≠ 0) (hRight : aRight ≠ 0) :
    update ratio aLeft aRight left center right =
      combine (1 - ratio * (aLeft + aRight) / 2)
        (ratio * aLeft / 2) (ratio * aRight / 2)
        center (splitState left (1 / aLeft)) (splitState right (-1 / aRight)) := by
  funext i
  simp only [update, interfaceFlux, combine, splitState]
  field_simp [hLeft, hRight]
  ring

theorem coefficients (ratio aLeft aRight : ℝ) (hRatio : 0 ≤ ratio)
    (hLeft : 0 < aLeft) (hRight : 0 < aRight)
    (hCflLeft : ratio * aLeft ≤ 1 / 2) (hCflRight : ratio * aRight ≤ 1 / 2) :
    1 / 2 ≤ 1 - ratio * (aLeft + aRight) / 2 ∧
      0 ≤ ratio * aLeft / 2 ∧ 0 ≤ ratio * aRight / 2 ∧
      (1 - ratio * (aLeft + aRight) / 2) + ratio * aLeft / 2 +
        ratio * aRight / 2 = 1 := by
  refine ⟨by nlinarith, by positivity, by positivity, by ring⟩

noncomputable def kineticTest (u v : ℝ) (q : Vec4) : ℝ :=
  q 3 - u * q 1 - v * q 2 + q 0 * (u^2 + v^2) / 2

theorem kineticTest_identity (q : Vec4) (hDensity : q 0 ≠ 0) (u v : ℝ) :
    kineticTest u v q = internalEnergy q +
      ((q 1 - q 0 * u)^2 + (q 2 - q 0 * v)^2) / (2 * q 0) := by
  simp only [kineticTest, internalEnergy]
  field_simp [hDensity]
  ring

theorem internalEnergy_le_test (q : Vec4) (hDensity : 0 < q 0) (u v : ℝ) :
    internalEnergy q ≤ kineticTest u v q := by
  rw [kineticTest_identity q (ne_of_gt hDensity)]
  exact le_add_of_nonneg_right (by positivity)

theorem kineticTest_at_velocity (q : Vec4) (hDensity : q 0 ≠ 0) :
    kineticTest (q 1 / q 0) (q 2 / q 0) q = internalEnergy q := by
  simp only [kineticTest, internalEnergy]
  field_simp [hDensity]
  ring

theorem combine_density_positive (a b c : ℝ) (q r s : Vec4)
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hq : 0 < q 0) (hr : 0 < r 0) (hs : 0 < s 0) :
    0 < combine a b c q r s 0 := by
  simp only [combine]
  positivity

theorem combine_internalEnergy_lower (a b c : ℝ) (q r s : Vec4)
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hq : 0 < q 0) (hr : 0 < r 0) (hs : 0 < s 0) :
    a * internalEnergy q + b * internalEnergy r + c * internalEnergy s ≤
      internalEnergy (combine a b c q r s) := by
  let result := combine a b c q r s
  let u := result 1 / result 0
  let v := result 2 / result 0
  have hResult : 0 < result 0 := combine_density_positive a b c q r s ha hb hc hq hr hs
  calc
    a * internalEnergy q + b * internalEnergy r + c * internalEnergy s ≤
        a * kineticTest u v q + b * kineticTest u v r + c * kineticTest u v s :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (internalEnergy_le_test q hq u v) ha.le)
        (mul_le_mul_of_nonneg_left (internalEnergy_le_test r hr u v) hb))
        (mul_le_mul_of_nonneg_left (internalEnergy_le_test s hs u v) hc)
    _ = kineticTest u v result := by simp only [kineticTest, result, combine]; ring
    _ = internalEnergy result := kineticTest_at_velocity result (ne_of_gt hResult)

noncomputable def energyMargin (q : Vec4) : ℝ :=
  2 * q 0 * q 3 - (q 1)^2 - (q 2)^2

theorem internalEnergy_eq_margin (q : Vec4) (hDensity : q 0 ≠ 0) :
    internalEnergy q = energyMargin q / (2 * q 0) := by
  simp only [internalEnergy, energyMargin]
  field_simp [hDensity]
  ring

theorem split_density (q : Vec4) (b : ℝ) (hDensity : q 0 ≠ 0) :
    splitState q b 0 = q 0 * (1 + b * (q 1 / q 0)) := by
  simp [splitState, physicalFlux]
  field_simp [hDensity]

theorem split_energyMargin (q : Vec4) (b : ℝ) (hDensity : q 0 ≠ 0) :
    energyMargin (splitState q b) =
      (1 + b * (q 1 / q 0))^2 * energyMargin q - (b * pressure q)^2 := by
  simp [energyMargin, splitState, physicalFlux]
  field_simp [hDensity]
  ring

theorem split_internalEnergy_lower (q : Vec4) (b theta : ℝ)
    (hDensity : 0 < q 0) (hFactor : 0 < 1 + b * (q 1 / q 0))
    (hLoss : (b * pressure q)^2 ≤
      theta * (1 + b * (q 1 / q 0))^2 * energyMargin q) :
    0 < splitState q b 0 ∧
      (1 - theta) * (1 + b * (q 1 / q 0)) * internalEnergy q ≤
        internalEnergy (splitState q b) := by
  have hSplit : 0 < splitState q b 0 := by
    rw [split_density q b (ne_of_gt hDensity)]
    exact mul_pos hDensity hFactor
  refine ⟨hSplit, ?_⟩
  rw [internalEnergy_eq_margin (splitState q b) (ne_of_gt hSplit)]
  apply (le_div_iff₀ (by positivity : 0 < 2 * splitState q b 0)).mpr
  rw [split_density q b (ne_of_gt hDensity),
    internalEnergy_eq_margin q (ne_of_gt hDensity),
    split_energyMargin q b (ne_of_gt hDensity)]
  have hCancel :
      (1 - theta) * (1 + b * (q 1 / q 0)) * (energyMargin q / (2 * q 0)) *
        (2 * (q 0 * (1 + b * (q 1 / q 0)))) =
      (1 - theta) * (1 + b * (q 1 / q 0))^2 * energyMargin q := by
    field_simp [ne_of_gt hDensity]
  rw [hCancel]
  nlinarith

theorem energyMargin_positive (q : Vec4)
    (hDensity : 0 < q 0) (hInternal : 0 < internalEnergy q) :
    0 < energyMargin q := by
  rw [internalEnergy_eq_margin q (ne_of_gt hDensity)] at hInternal
  exact (div_pos_iff_of_pos_right (by positivity : 0 < 2 * q 0)).mp hInternal

theorem wave_factor (u c b : ℝ) (hc : 0 < c)
    (hWave : |b| * (|u| + c) ≤ 1) :
    0 < 1 + b * u ∧ |b| * c ≤ 1 + b * u := by
  have hProduct := neg_abs_le (b * u)
  rw [abs_mul] at hProduct
  have hLower : |b| * c ≤ 1 + b * u := by nlinarith
  refine ⟨?_, hLower⟩
  by_cases hb : b = 0
  · simp [hb]
  · exact lt_of_lt_of_le (mul_pos (abs_pos.mpr hb) hc) hLower

theorem sound_pressure_identity (q : Vec4) (c : ℝ) (hDensity : q 0 ≠ 0)
    (hSound : c^2 = (7 / 5) * pressure q / q 0) :
    7 * (pressure q)^2 = c^2 * energyMargin q := by
  rw [hSound]
  simp only [pressure, internalEnergy, energyMargin]
  field_simp [hDensity]
  ring

theorem split_sound_lower (q : Vec4) (b c : ℝ)
    (hDensity : 0 < q 0) (hInternal : 0 < internalEnergy q)
    (hc : 0 < c) (hSound : c^2 = (7 / 5) * pressure q / q 0)
    (hWave : |b| * (|q 1 / q 0| + c) ≤ 1) :
    0 < splitState q b 0 ∧
      (6 / 7) * (1 + b * (q 1 / q 0)) * internalEnergy q ≤
        internalEnergy (splitState q b) := by
  obtain ⟨hFactor, hLower⟩ := wave_factor (q 1 / q 0) c b hc hWave
  have hMargin := energyMargin_positive q hDensity hInternal
  have hSquare : (b * c)^2 ≤ (1 + b * (q 1 / q 0))^2 := by
    have hAbs : |b * c| ≤ 1 + b * (q 1 / q 0) := by
      simpa only [abs_mul, abs_of_pos hc] using hLower
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (b * c)) hFactor.le).mpr hAbs
  have hWeighted := mul_le_mul_of_nonneg_right hSquare hMargin.le
  have hIdentity := sound_pressure_identity q c (ne_of_gt hDensity) hSound
  have hLoss : (b * pressure q)^2 ≤
      (1 / 7) * (1 + b * (q 1 / q 0))^2 * energyMargin q := by
    have hScaled := congrArg (fun x : ℝ => b^2 * x) hIdentity
    nlinarith only [hWeighted, hScaled]
  have hResult := split_internalEnergy_lower q b (1 / 7) hDensity hFactor hLoss
  norm_num only at hResult
  exact hResult

#print axioms update_decomposition
#print axioms coefficients
#print axioms kineticTest_identity
#print axioms combine_internalEnergy_lower
#print axioms split_energyMargin
#print axioms split_internalEnergy_lower
#print axioms wave_factor
#print axioms sound_pressure_identity
#print axioms split_sound_lower

end Project.EulerRiemann.RealRusanov
