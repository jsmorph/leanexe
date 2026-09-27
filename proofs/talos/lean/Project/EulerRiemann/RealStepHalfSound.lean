import Project.EulerRiemann.RealStep

namespace Project.EulerRiemann.RealRusanov
open Project.Euler2DConservative.Guard (Vec4 internalEnergy pressure)

theorem split_half_sound_lower (q : Vec4) (b c : ℝ)
    (hDensity : 0 < q 0) (hInternal : 0 < internalEnergy q)
    (hc : 0 < c) (hSound : c^2 = (7 / 5) * pressure q / q 0)
    (hWave : |b| * (|q 1 / q 0| + c / 2) ≤ 1) :
    0 < splitState q b 0 ∧
      (3 / 7) * (1 + b * (q 1 / q 0)) * internalEnergy q ≤
        internalEnergy (splitState q b) := by
  obtain ⟨hFactor, hLower⟩ := wave_factor (q 1 / q 0) (c / 2) b (by positivity) hWave
  have hMargin := energyMargin_positive q hDensity hInternal
  have hSquare : (b * c)^2 ≤ 4 * (1 + b * (q 1 / q 0))^2 := by
    have hAbs : |b * c| ≤ 2 * (1 + b * (q 1 / q 0)) := by
      rw [abs_mul, abs_of_pos hc]
      nlinarith only [hLower]
    have h := (sq_le_sq₀ (abs_nonneg (b * c)) (by positivity :
      0 ≤ 2 * (1 + b * (q 1 / q 0)))).mpr hAbs
    rw [sq_abs] at h
    nlinarith only [h]
  have hWeighted := mul_le_mul_of_nonneg_right hSquare hMargin.le
  have hIdentity := sound_pressure_identity q c (ne_of_gt hDensity) hSound
  have hLoss : (b * pressure q)^2 ≤
      (4 / 7) * (1 + b * (q 1 / q 0))^2 * energyMargin q := by
    have hScaled := congrArg (fun x : ℝ => b^2 * x) hIdentity
    nlinarith only [hWeighted, hScaled]
  have hResult := split_internalEnergy_lower q b (4 / 7) hDensity hFactor hLoss
  norm_num only at hResult
  exact hResult

theorem split_half_sound_positive (q : Vec4) (b c : ℝ)
    (hDensity : 0 < q 0) (hInternal : 0 < internalEnergy q)
    (hc : 0 < c) (hSound : c^2 = (7 / 5) * pressure q / q 0)
    (hWave : |b| * (|q 1 / q 0| + c / 2) ≤ 1) :
    0 < splitState q b 0 ∧ 0 < internalEnergy (splitState q b) := by
  obtain ⟨hr, he⟩ := split_half_sound_lower q b c hDensity hInternal hc hSound hWave
  have hw := (wave_factor (q 1 / q 0) (c / 2) b (by positivity) hWave).1
  exact ⟨hr, lt_of_lt_of_le (by positivity) he⟩

theorem update_half_sound_positive (ratio aLeft aRight cLeft cRight : ℝ)
    (left center right : Vec4)
    (hRatio : 0 ≤ ratio) (hLeft : 0 < aLeft) (hRight : 0 < aRight)
    (hCflLeft : ratio * aLeft ≤ 1 / 2) (hCflRight : ratio * aRight ≤ 1 / 2)
    (hLeftState : 0 < left 0 ∧ 0 < internalEnergy left)
    (hCenterState : 0 < center 0 ∧ 0 < internalEnergy center)
    (hRightState : 0 < right 0 ∧ 0 < internalEnergy right)
    (hcLeft : 0 < cLeft) (hcRight : 0 < cRight)
    (hSoundLeft : cLeft^2 = (7 / 5) * pressure left / left 0)
    (hSoundRight : cRight^2 = (7 / 5) * pressure right / right 0)
    (hWaveLeft : |left 1 / left 0| + cLeft / 2 ≤ aLeft)
    (hWaveRight : |right 1 / right 0| + cRight / 2 ≤ aRight) :
    center 0 / 2 ≤ update ratio aLeft aRight left center right 0 ∧
      internalEnergy center / 2 ≤
        internalEnergy (update ratio aLeft aRight left center right) ∧
      0 < update ratio aLeft aRight left center right 0 ∧
      0 < internalEnergy (update ratio aLeft aRight left center right) := by
  have hWave (u c a : ℝ) (ha : 0 < a) (h : |u| + c / 2 ≤ a) :
      |1 / a| * (|u| + c / 2) ≤ 1 := by
    rw [abs_of_pos (by positivity : 0 < 1 / a), one_div, inv_mul_eq_div]
    exact (div_le_one ha).mpr h
  have hl := split_half_sound_positive left (1 / aLeft) cLeft hLeftState.1 hLeftState.2
    hcLeft hSoundLeft (hWave _ _ _ hLeft hWaveLeft)
  have hr := split_half_sound_positive right (-1 / aRight) cRight hRightState.1 hRightState.2
    hcRight hSoundRight (by
      simpa only [neg_div, abs_neg] using hWave _ _ _ hRight hWaveRight)
  exact update_positive_of_splits ratio aLeft aRight left center right
    hRatio hLeft hRight hCflLeft hCflRight hCenterState hl hr

#print axioms split_half_sound_lower
#print axioms split_half_sound_positive
#print axioms update_half_sound_positive
end Project.EulerRiemann.RealRusanov
