import Project.EulerRiemann.FrozenOutwardMesh
import Project.EulerRiemann.FrozenOutwardCflSpec
import Project.EulerRiemann.FrozenTimeBounds

namespace Project.EulerRiemann.Frozen.OutwardCfl
open CodeLib.IEEE64
open Project.ProofKit.F64Outward
open Project.ProofKit.F64Order

theorem spacing_lower (n : Nat) (hn : n ≤ 800) (hs : (spacingLower n).status = 0) :
    value (spacingLower n).value ≤ 1/(n:ℝ) := by
  have h := sound_lower (div_accepted false 0x3FF0000000000000
    (Time.smallNaturalBits n) hs).2.2.2
  have hword : Time.smallNaturalBits 1 = 0x3FF0000000000000 := by decide +kernel
  have hone : value 0x3FF0000000000000 = (1:ℝ) := by
    simpa only [hword, Nat.cast_one] using Time.smallNaturalBits_value 1 (by decide)
  simpa only [spacingLower, hone, Time.smallNaturalBits_value n hn] using h.2

theorem grid_ratio_accepted (n : Nat) (dt alpha : UInt64)
    (hs : (gridRatioChecked n dt alpha).status = 0) :
    2 ≤ n ∧ n ≤ 800 ∧ positiveBits dt = true ∧ positiveBits alpha = true ∧
    positiveBits (gridRatioChecked n dt alpha).value = true ∧
    value dt*(n:ℝ) ≤ value (gridRatioChecked n dt alpha).value ∧
    value (gridRatioChecked n dt alpha).value*value alpha ≤ (1:ℝ)/2 := by
  unfold gridRatioChecked at hs ⊢
  dsimp only at hs ⊢
  split_ifs at hs with hn hh
  · simp only [hn, hh, ite_true, true_and]
    have hh : (spacingLower n).status = 0 := by simpa using hh
    have hb := ratio_accepted dt (spacingLower n).value alpha hs
    have hnPos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hdPos := (positiveBits_spec dt hb.1).2
    have hhPos := (positiveBits_spec (spacingLower n).value hb.2.1).2
    have hhBound := (le_div_iff₀ hnPos).mp (spacing_lower n hn.2 hh)
    have hr : value dt*(n:ℝ) ≤ value dt/value (spacingLower n).value := by
      apply (le_div_iff₀ hhPos).mpr
      calc
        value dt*(n:ℝ)*value (spacingLower n).value =
            value dt*(value (spacingLower n).value*(n:ℝ)) := by ring
        _ ≤ value dt*1 := mul_le_mul_of_nonneg_left hhBound hdPos.le
        _ = value dt := mul_one _
    exact ⟨hb.1, hb.2.2.1, hb.2.2.2.1,
      hr.trans hb.2.2.2.2.1, hb.2.2.2.2.2⟩
  all_goals exact False.elim ((by decide : (1:UInt64) ≠ 0) hs)

theorem exact_grid_courant (n : Nat) (dt alpha : UInt64)
    (hs : (gridRatioChecked n dt alpha).status = 0) :
    value dt*(n:ℝ)*value alpha ≤ (1:ℝ)/2 := by
  have h := grid_ratio_accepted n dt alpha hs
  exact (mul_le_mul_of_nonneg_right h.2.2.2.2.2.1
    (positiveBits_spec alpha h.2.2.2.1).2.le).trans h.2.2.2.2.2.2

theorem grid_ratio_behavior (n : Nat) (dt alpha : UInt64) :
    gridRatioChecked n dt alpha = rejected ∨
      (gridRatioChecked n dt alpha).status = 0 ∧
      positiveBits (gridRatioChecked n dt alpha).value = true ∧
      value dt*(n:ℝ) ≤ value (gridRatioChecked n dt alpha).value ∧
      value (gridRatioChecked n dt alpha).value*value alpha ≤ (1:ℝ)/2 := by
  have hresult : gridRatioChecked n dt alpha = rejected ∨
      (gridRatioChecked n dt alpha).status = 0 := by
    unfold gridRatioChecked
    dsimp only
    split_ifs
    · exact (ratio_behavior _ _ _).imp id (fun h => h.1)
    all_goals exact Or.inl rfl
  rcases hresult with hr | hs
  · exact Or.inl hr
  · exact Or.inr ⟨hs, (grid_ratio_accepted n dt alpha hs).2.2.2.2⟩

theorem bounded_speed_grid_courant (n : Nat) (dt alpha : UInt64)
    (hs : (gridRatioChecked n dt alpha).status = 0)
    (speed : ℝ) (hSpeed : speed ≤ value alpha) :
    value dt*(n:ℝ)*speed ≤ (1:ℝ)/2 := by
  have h := grid_ratio_accepted n dt alpha hs
  have hratio := mul_nonneg (positiveBits_spec dt h.2.2.1).2.le (Nat.cast_nonneg n)
  exact (mul_le_mul_of_nonneg_left hSpeed hratio).trans (exact_grid_courant n dt alpha hs)

#print axioms spacing_lower
#print axioms grid_ratio_accepted
#print axioms exact_grid_courant
#print axioms grid_ratio_behavior
#print axioms bounded_speed_grid_courant
end Project.EulerRiemann.Frozen.OutwardCfl
