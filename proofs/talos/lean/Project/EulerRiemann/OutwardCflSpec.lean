import Project.EulerRiemann.OutwardCfl
import Project.EulerRiemann.OutwardConstants
import Project.ProofKit.F64OutwardAccepted
import Project.ProofKit.F64OrderComplete

namespace Project.EulerRiemann.OutwardCfl
open CodeLib.IEEE64
open Project.ProofKit.F64Outward
open Project.ProofKit.F64Order

theorem ratio_accepted (dt spacing alpha : UInt64)
    (hs : (ratioChecked dt spacing alpha).status = 0) :
    positiveBits dt = true ∧ positiveBits spacing = true ∧ positiveBits alpha = true ∧
    positiveBits (ratioChecked dt spacing alpha).value = true ∧
    value dt/value spacing ≤ value (ratioChecked dt spacing alpha).value ∧
    value (ratioChecked dt spacing alpha).value*value alpha ≤ (1:ℝ)/2 := by
  let ratio := div true dt spacing
  let courant := mul true ratio.value alpha
  unfold ratioChecked at hs ⊢
  dsimp only at hs ⊢
  split_ifs at hs with hp hr hc
  · simp only [hp, hr, hc, ite_true]
    have hp : (positiveBits dt = true ∧ positiveBits spacing = true) ∧
        positiveBits alpha = true := by simpa using hp
    have hr : ratio.status = 0 := by simpa [ratio] using hr
    have hc : courant.status = 0 ∧ courant.value ≤ 0x3FE0000000000000 := by
      simpa [courant, ratio] using hc
    have ed := sound_upper (div_accepted true dt spacing hr).2.2.2
    have em := sound_upper (mul_accepted true ratio.value alpha hc.1).2.2
    have hdt := (positiveBits_spec dt hp.1.1).2
    have hspacing := (positiveBits_spec spacing hp.1.2).2
    have halpha := (positiveBits_spec alpha hp.2).2
    have hratio : 0 < value ratio.value := (div_pos hdt hspacing).trans_le ed.2
    have hcourant : 0 < value courant.value := (mul_pos hratio halpha).trans_le em.2
    have pr := positiveBits_of_finite_value_pos ratio.value ed.1 hratio
    have pc := positiveBits_of_finite_value_pos courant.value em.1 hcourant
    have ph : positiveBits 0x3FE0000000000000 = true := by decide
    have hb := abs_value_mono courant.value 0x3FE0000000000000 (by
      simpa only [absBits_of_positive _ pc, absBits_of_positive _ ph] using hc.2)
    rw [abs_of_pos hcourant, OutwardSpeed.half_value, abs_of_pos (by norm_num : (0:ℝ) < 1/2)] at hb
    exact ⟨hp.1.1, hp.1.2, hp.2, pr, ed.2, em.2.trans hb⟩
  all_goals exact False.elim ((by decide : (1:UInt64) ≠ 0) hs)

theorem exact_courant (dt spacing alpha : UInt64)
    (hs : (ratioChecked dt spacing alpha).status = 0) :
    value dt/value spacing*value alpha ≤ (1:ℝ)/2 := by
  have h := ratio_accepted dt spacing alpha hs
  exact (mul_le_mul_of_nonneg_right h.2.2.2.2.1
    (positiveBits_spec alpha h.2.2.1).2.le).trans h.2.2.2.2.2

theorem bounded_speed_courant (dt spacing alpha : UInt64)
    (hs : (ratioChecked dt spacing alpha).status = 0)
    (speed : ℝ) (hSpeed : speed ≤ value alpha) :
    value dt/value spacing*speed ≤ (1:ℝ)/2 := by
  have h := ratio_accepted dt spacing alpha hs
  have hratio := div_nonneg (positiveBits_spec dt h.1).2.le
    (positiveBits_spec spacing h.2.1).2.le
  exact (mul_le_mul_of_nonneg_left hSpeed hratio).trans (exact_courant dt spacing alpha hs)

theorem ratio_behavior (dt spacing alpha : UInt64) :
    ratioChecked dt spacing alpha = rejected ∨
      (ratioChecked dt spacing alpha).status = 0 ∧
      positiveBits (ratioChecked dt spacing alpha).value = true ∧
      value dt/value spacing ≤ value (ratioChecked dt spacing alpha).value ∧
      value (ratioChecked dt spacing alpha).value*value alpha ≤ (1:ℝ)/2 := by
  have hresult : ratioChecked dt spacing alpha = rejected ∨
      (ratioChecked dt spacing alpha).status = 0 := by
    unfold ratioChecked
    dsimp only
    split_ifs with hp hr hc
    · exact Or.inr (by simpa using hr)
    all_goals exact Or.inl rfl
  rcases hresult with hr | hs
  · exact Or.inl hr
  · exact Or.inr ⟨hs, (ratio_accepted dt spacing alpha hs).2.2.2⟩

#print axioms ratio_accepted
#print axioms exact_courant
#print axioms bounded_speed_courant
#print axioms ratio_behavior
end Project.EulerRiemann.OutwardCfl
