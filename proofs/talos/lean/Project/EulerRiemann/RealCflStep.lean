import Project.EulerRiemann.RealRusanov

namespace Project.EulerRiemann.RealRusanov
open Project.Euler2DConservative.Guard (Vec4 internalEnergy)

theorem update_positive_weight (ratio aLeft aRight weight : ℝ) (left center right : Vec4)
    (hRatio : 0 ≤ ratio) (hLeft : 0 < aLeft) (hRight : 0 < aRight) (hw : 0 < weight)
    (hCfl : ratio * (aLeft + aRight) / 2 ≤ 1 - weight)
    (hCenter : 0 < center 0 ∧ 0 < internalEnergy center)
    (hSplitLeft : 0 < splitState left (1 / aLeft) 0 ∧
      0 < internalEnergy (splitState left (1 / aLeft)))
    (hSplitRight : 0 < splitState right (-1 / aRight) 0 ∧
      0 < internalEnergy (splitState right (-1 / aRight))) :
    weight * center 0 ≤ update ratio aLeft aRight left center right 0 ∧
      weight * internalEnergy center ≤ internalEnergy (update ratio aLeft aRight left center right) ∧
      0 < update ratio aLeft aRight left center right 0 ∧
      0 < internalEnergy (update ratio aLeft aRight left center right) := by
  let a := 1 - ratio * (aLeft + aRight) / 2
  let b := ratio * aLeft / 2
  let c := ratio * aRight / 2
  have ha : weight ≤ a := by dsimp only [a]; linarith only [hCfl]
  have haPos : 0 < a := hw.trans_le ha
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  have hd := update_decomposition ratio aLeft aRight left center right (ne_of_gt hLeft) (ne_of_gt hRight)
  have hConcave := combine_internalEnergy_lower a b c center
    (splitState left (1 / aLeft)) (splitState right (-1 / aRight))
    haPos hb hc hCenter.1 hSplitLeft.1 hSplitRight.1
  have hrho : weight * center 0 ≤ update ratio aLeft aRight left center right 0 := by
    rw [hd]
    change weight * center 0 ≤ a * center 0 + b * splitState left (1 / aLeft) 0 +
      c * splitState right (-1 / aRight) 0
    have h := mul_le_mul_of_nonneg_right ha hCenter.1.le
    have hl := mul_nonneg hb hSplitLeft.1.le
    have hr := mul_nonneg hc hSplitRight.1.le
    linarith only [h, hl, hr]
  have he : weight * internalEnergy center ≤ internalEnergy (update ratio aLeft aRight left center right) := by
    rw [hd]
    have h := mul_le_mul_of_nonneg_right ha hCenter.2.le
    have hl := mul_nonneg hb hSplitLeft.2.le
    have hr := mul_nonneg hc hSplitRight.2.le
    change weight * internalEnergy center ≤ internalEnergy
      (combine a b c center (splitState left (1 / aLeft)) (splitState right (-1 / aRight)))
    linarith only [h, hl, hr, hConcave]
  exact ⟨hrho, he, (mul_pos hw hCenter.1).trans_le hrho, (mul_pos hw hCenter.2).trans_le he⟩

#print axioms update_positive_weight
end Project.EulerRiemann.RealRusanov
