import Project.EulerGridScan.Iteration

namespace Project.EulerGridScan.Execution
open Project.EulerGridStep
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- The result still owed by an in-progress loop state. -/
def remaining (input : Array UInt64) (count index : Nat) (status speed : UInt64) : Model.CheckedSpeed :=
  if status == 0 then Model.scan input index speed (count - index) else ⟨status, speed⟩

theorem scan_one_status (input : Array UInt64) (index : Nat) (speed : UInt64) :
    (Model.scan input index speed 1).status = 0 ∨
      (Model.scan input index speed 1).status = 1 ∧ (Model.scan input index speed 1).speed = 0 := by
  rw [show 1 = 0 + 1 from rfl, Scan.scan_succ]
  split <;> simp [Model.scan]

theorem scan_compose (input : Array UInt64) (index fuel : Nat) (speed : UInt64) :
    Model.scan input index speed (fuel + 1) =
      let next := Model.scan input index speed 1
      if next.status == 0 then Model.scan input (index + 1) next.speed fuel else next := by
  rw [Scan.scan_succ]
  rw [show 1 = 0 + 1 from rfl, Scan.scan_succ]
  generalize Scan.stateAt input index = state
  split <;> simp [Model.scan]

theorem remaining_step (input : Array UInt64) (count index : Nat) (speed : UInt64)
    (hi : index < count) :
    let next := Model.scan input index speed 1
    remaining input count (index + 1) next.status next.speed =
      remaining input count index 0 speed := by
  have hcount : count - index = (count - (index + 1)) + 1 := by omega
  simp only [remaining, beq_self_eq_true, ite_true]
  rw [hcount]
  conv_rhs => rw [scan_compose]

theorem remaining_done (input : Array UInt64) (count index : Nat) (status speed : UInt64)
    (hi : index ≤ count) (hdone : ¬ (index < count ∧ status = 0)) :
    remaining input count index status speed = ⟨status, speed⟩ := by
  unfold remaining
  by_cases hs : status = 0
  · have hnot : ¬ index < count := fun hlt => hdone ⟨hlt, hs⟩
    have heq : index = count := by omega
    subst index
    simp [hs, Model.scan]
  · simp [hs]

#print axioms remaining_step
#print axioms remaining_done
end Project.EulerGridScan.Execution
