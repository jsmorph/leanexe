import Project.EulerReconstructed.Control
import Project.EulerReconstructed.TraversalSafety
import Project.EulerRiemann.TraversalModel
import Project.EulerRiemann.TimeBounds

namespace Project.EulerReconstructed.Control
open Project.EulerRiemann
open Project.EulerRiemann.Traversal (Cell Indexed accepted)
open Project.EulerReconstructed.Traversal (step step_indexed)

theorem retry_status (fuel n trials : Nat) (time dt alpha : UInt64) (grid : Array Cell) :
    (retry fuel n trials time dt alpha grid).status = 0 ∨
      (retry fuel n trials time dt alpha grid).status = 3 ∨
      (retry fuel n trials time dt alpha grid).status = 4 := by
  induction fuel generalizing dt with
  | zero => simp [retry]
  | succ fuel ih =>
    simp only [retry]
    split
    · split
      · split
        · simp
        · exact ih _
      · exact ih _
    · simp

theorem retry_success (fuel n trials : Nat) (time dt alpha : UInt64) (grid : Array Cell)
    (h : (retry fuel n trials time dt alpha grid).status = 0) :
    let out := retry fuel n trials time dt alpha grid
    Time.validAdvance time out.dt = true ∧
      (OutwardCfl.gridRatioChecked n out.dt alpha).status = 0 ∧
      accepted out.grid = true ∧
      out.grid = step n trials (OutwardCfl.gridRatioChecked n out.dt alpha).value grid := by
  revert h
  induction fuel generalizing dt with
  | zero => simp [retry]
  | succ fuel ih =>
    simp only [retry]
    split
    · split
      · split
        · rename_i ht hr ha
          intro _
          exact ⟨ht, by simpa only [beq_iff_eq] using hr, ha, rfl⟩
        · exact ih _
      · exact ih _
    · simp

theorem retry_indexed (fuel n trials : Nat) (time dt alpha : UInt64) (grid : Array Cell)
    (hg : Indexed n grid) (h : (retry fuel n trials time dt alpha grid).status = 0) :
    Indexed n (retry fuel n trials time dt alpha grid).grid := by
  rw [(retry_success fuel n trials time dt alpha grid h).2.2.2]
  exact step_indexed n trials _ grid hg

#print axioms retry_status
#print axioms retry_success
#print axioms retry_indexed
end Project.EulerReconstructed.Control
