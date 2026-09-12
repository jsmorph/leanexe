import Project.EulerRiemann.RealRusanov

namespace Project.EulerRiemann.RealRusanov
open Project.Euler2DConservative.Guard (Vec4 internalEnergy pressure)

theorem split_positive (q : Vec4) (b c : ℝ)
    (hDensity : 0 < q 0) (hInternal : 0 < internalEnergy q)
    (hc : 0 < c) (hSound : c^2 = (7 / 5) * pressure q / q 0)
    (hWave : |b| * (|q 1 / q 0| + c) ≤ 1) :
    0 < splitState q b 0 ∧ 0 < internalEnergy (splitState q b) := by
  obtain ⟨hr, he⟩ := split_sound_lower q b c hDensity hInternal hc hSound hWave
  have hw := (wave_factor (q 1 / q 0) c b hc hWave).1
  exact ⟨hr, lt_of_lt_of_le (by positivity) he⟩

theorem update_lower_of_splits (ratio aLeft aRight : ℝ) (left center right : Vec4)
    (hRatio : 0 ≤ ratio) (hLeft : 0 < aLeft) (hRight : 0 < aRight)
    (hCflLeft : ratio * aLeft ≤ 1 / 2) (hCflRight : ratio * aRight ≤ 1 / 2)
    (hCenter : 0 < center 0 ∧ 0 < internalEnergy center)
    (hSplitLeft : 0 < splitState left (1 / aLeft) 0 ∧
      0 < internalEnergy (splitState left (1 / aLeft)))
    (hSplitRight : 0 < splitState right (-1 / aRight) 0 ∧
      0 < internalEnergy (splitState right (-1 / aRight))) :
    (1 - ratio * (aLeft + aRight) / 2) * center 0 ≤
        update ratio aLeft aRight left center right 0 ∧
      (1 - ratio * (aLeft + aRight) / 2) * internalEnergy center ≤
        internalEnergy (update ratio aLeft aRight left center right) := by
  obtain ⟨ha, hb, hc, _⟩ := coefficients ratio aLeft aRight
    hRatio hLeft hRight hCflLeft hCflRight
  rw [update_decomposition ratio aLeft aRight left center right
    (ne_of_gt hLeft) (ne_of_gt hRight)]
  constructor
  · dsimp only [combine]
    have hl := mul_nonneg hb hSplitLeft.1.le
    have hr := mul_nonneg hc hSplitRight.1.le
    linarith
  · have hConcave := combine_internalEnergy_lower
      (1 - ratio * (aLeft + aRight) / 2) (ratio * aLeft / 2) (ratio * aRight / 2)
      center (splitState left (1 / aLeft)) (splitState right (-1 / aRight))
      (by linarith) hb hc hCenter.1 hSplitLeft.1 hSplitRight.1
    have hl := mul_nonneg hb hSplitLeft.2.le
    have hr := mul_nonneg hc hSplitRight.2.le
    linarith

theorem update_positive (ratio aLeft aRight cLeft cRight : ℝ)
    (left center right : Vec4)
    (hRatio : 0 ≤ ratio) (hLeft : 0 < aLeft) (hRight : 0 < aRight)
    (hCflLeft : ratio * aLeft ≤ 1 / 2) (hCflRight : ratio * aRight ≤ 1 / 2)
    (hLeftState : 0 < left 0 ∧ 0 < internalEnergy left)
    (hCenterState : 0 < center 0 ∧ 0 < internalEnergy center)
    (hRightState : 0 < right 0 ∧ 0 < internalEnergy right)
    (hcLeft : 0 < cLeft) (hcRight : 0 < cRight)
    (hSoundLeft : cLeft^2 = (7 / 5) * pressure left / left 0)
    (hSoundRight : cRight^2 = (7 / 5) * pressure right / right 0)
    (hWaveLeft : |left 1 / left 0| + cLeft ≤ aLeft)
    (hWaveRight : |right 1 / right 0| + cRight ≤ aRight) :
    center 0 / 2 ≤ update ratio aLeft aRight left center right 0 ∧
      internalEnergy center / 2 ≤
        internalEnergy (update ratio aLeft aRight left center right) ∧
      0 < update ratio aLeft aRight left center right 0 ∧
      0 < internalEnergy (update ratio aLeft aRight left center right) := by
  have hWave (u c a : ℝ) (ha : 0 < a) (h : |u| + c ≤ a) :
      |1 / a| * (|u| + c) ≤ 1 := by
    rw [abs_of_pos (by positivity : 0 < 1 / a), one_div, inv_mul_eq_div]
    exact (div_le_one ha).mpr h
  have hl := split_positive left (1 / aLeft) cLeft hLeftState.1 hLeftState.2
    hcLeft hSoundLeft (hWave _ _ _ hLeft hWaveLeft)
  have hr := split_positive right (-1 / aRight) cRight hRightState.1 hRightState.2
    hcRight hSoundRight (by
      simpa only [neg_div, abs_neg] using hWave _ _ _ hRight hWaveRight)
  obtain ⟨hrho, he⟩ := update_lower_of_splits ratio aLeft aRight left center right
    hRatio hLeft hRight hCflLeft hCflRight hCenterState hl hr
  have ha := (coefficients ratio aLeft aRight hRatio hLeft hRight hCflLeft hCflRight).1
  have hrhoLower : center 0 / 2 ≤ update ratio aLeft aRight left center right 0 := by
    nlinarith [mul_le_mul_of_nonneg_right ha hCenterState.1.le]
  have heLower : internalEnergy center / 2 ≤
      internalEnergy (update ratio aLeft aRight left center right) := by
    nlinarith [mul_le_mul_of_nonneg_right ha hCenterState.2.le]
  exact ⟨hrhoLower, heLower,
    lt_of_lt_of_le (div_pos hCenterState.1 (by norm_num)) hrhoLower,
    lt_of_lt_of_le (div_pos hCenterState.2 (by norm_num)) heLower⟩

#print axioms split_positive
#print axioms update_lower_of_splits
#print axioms update_positive
end Project.EulerRiemann.RealRusanov
