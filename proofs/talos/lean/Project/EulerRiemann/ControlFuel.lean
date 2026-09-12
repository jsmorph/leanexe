import Project.EulerRiemann.ControlTime

namespace Project.EulerRiemann.Control

theorem advance_fuel_sufficient (fuel n : Nat) (time : UInt64)
    (grid : Array Traversal.Cell)
    (hf : Time.endTime.toNat - time.toNat < fuel) :
    (advance fuel n time grid).status ≠ 5 := by
  induction fuel generalizing time grid with
  | zero => omega
  | succ fuel ih =>
    simp only [advance]
    split
    · simp
    · split
      · split
        · rename_i ht hs ha
          apply ih
          have hsuccess := retry_success _ _ _ _ _ (by simpa using ha)
          have hdecrease := Time.remaining_decreases _ _ hsuccess.1
          omega
        · rcases retry_status (Time.proposal n time (Traversal.scan grid).alpha).toNat.succ
              n time (Time.proposal n time (Traversal.scan grid).alpha) grid with h | h | h
          all_goals simp [h]
      · simp

theorem run_fuel_sufficient (n : Nat) : (run n).status ≠ 5 := by
  simp only [run]
  split
  · apply advance_fuel_sufficient
    simp
  · decide

#print axioms advance_fuel_sufficient
#print axioms run_fuel_sufficient

end Project.EulerRiemann.Control
