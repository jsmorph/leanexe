import Project.EulerRiemann.OutwardMaximum
import Project.EulerRiemann.OutwardSpeedSpec
import Project.ProofKit.F64NonnegativeMaximum

namespace Project.EulerRiemann.OutwardMaximum
open Project.ProofKit.F64Outward (Checked rejected)
open Project.ProofKit.F64Order
open Project.Euler2DCellStep.Sweep (State)
open CodeLib.IEEE64

theorem merge_status (left right : Checked) :
    (merge left right).status = 0 ↔ left.status = 0 ∧ right.status = 0 := by
  simp only [merge]
  split_ifs with h
  · simpa using h
  · simpa [rejected] using h

theorem merge_value (left right : Checked) (h : (merge left right).status = 0) :
    (merge left right).value = max left.value right.value := by
  have hs := (merge_status left right).mp h
  simp [merge, hs.1, hs.2]

theorem merge_result (left right : Checked) :
    merge left right = rejected ∨ (merge left right).status = 0 := by
  unfold merge
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem merge_upper (left right : Checked) (h : (merge left right).status = 0)
    (hl : positiveBits left.value = true) (hr : positiveBits right.value = true) :
    positiveBits (merge left right).value = true ∧
      value (merge left right).value = max (value left.value) (value right.value) := by
  rw [merge_value left right h]
  exact positive_max_value left.value right.value hl hr

theorem interface_status (left right : State) :
    (interfaceUpper left right).status = 0 ↔
      (OutwardSpeed.speedUpper left.density left.mx left.my left.energy).status = 0 ∧
      (OutwardSpeed.speedUpper right.density right.mx right.my right.energy).status = 0 :=
  merge_status _ _

theorem cell_status (state : State) :
    (cellUpper state).status = 0 ↔
      (OutwardSpeed.speedUpper state.density state.mx state.my state.energy).status = 0 ∧
      (OutwardSpeed.speedUpper state.density state.my state.mx state.energy).status = 0 :=
  merge_status _ _

theorem cell_positive (state : State) (h : (cellUpper state).status = 0) :
    positiveBits (cellUpper state).value = true := by
  have hs := (cell_status state).mp h
  exact (merge_upper _ _ h
    (OutwardSpeed.speed_positive _ _ _ _ hs.1)
    (OutwardSpeed.speed_positive _ _ _ _ hs.2)).1

#print axioms merge_upper
#print axioms cell_positive

end Project.EulerRiemann.OutwardMaximum
