import Project.EulerCertificate.Control

namespace Project.EulerCertificate.Control
open Project.EulerRiemann.Traversal (Cell accepted)
open Project.EulerCertificate.Flux (Vector)

def Attempt.base (out : Attempt) : Project.EulerRiemann.Control.Attempt :=
  ⟨out.status, out.dt, out.grid⟩

def Result.base (out : Result) : Project.EulerRiemann.Control.Result :=
  ⟨out.status, out.time, out.grid⟩

theorem attempt_eq (n trials : Nat) (dt ratio : UInt64) (grid : Array Cell) :
    attempt n trials dt ratio grid =
      if accepted (Project.EulerReconstructed.Traversal.step n trials ratio grid) then
        some ⟨Project.EulerReconstructed.Traversal.step n trials ratio grid,
          Boundary.physicalStep n trials dt grid
            (Project.EulerReconstructed.Traversal.sweep n trials false ratio grid)⟩
      else none := by
  simp only [attempt, Project.EulerReconstructed.Traversal.step]
  split
  · split <;> simp_all only
  · simp_all only

theorem retry_base (fuel n trials : Nat) (time dt alpha : UInt64) (grid : Array Cell) :
    (retry fuel n trials time dt alpha grid).base =
      Project.EulerReconstructed.Control.retry fuel n trials time dt alpha grid := by
  induction fuel generalizing dt with
  | zero => rfl
  | succ fuel ih =>
    simp only [retry, Project.EulerReconstructed.Control.retry, attempt_eq]
    split
    · split
      · by_cases ha : accepted (Project.EulerReconstructed.Traversal.step n trials
            (Project.EulerRiemann.OutwardCfl.gridRatioChecked n dt alpha).value grid) = true
        · simp [ha, Attempt.base]
        · simp only [ha, ite_false]
          exact ih _
      · exact ih _
    · rfl

theorem retry_status (fuel n trials : Nat) (time dt alpha : UInt64) (grid : Array Cell) :
    (retry fuel n trials time dt alpha grid).status =
      (Project.EulerReconstructed.Control.retry fuel n trials time dt alpha grid).status :=
  congrArg Project.EulerRiemann.Control.Attempt.status (retry_base fuel n trials time dt alpha grid)

theorem retry_dt (fuel n trials : Nat) (time dt alpha : UInt64) (grid : Array Cell) :
    (retry fuel n trials time dt alpha grid).dt =
      (Project.EulerReconstructed.Control.retry fuel n trials time dt alpha grid).dt :=
  congrArg Project.EulerRiemann.Control.Attempt.dt (retry_base fuel n trials time dt alpha grid)

theorem retry_grid (fuel n trials : Nat) (time dt alpha : UInt64) (grid : Array Cell) :
    (retry fuel n trials time dt alpha grid).grid =
      (Project.EulerReconstructed.Control.retry fuel n trials time dt alpha grid).grid :=
  congrArg Project.EulerRiemann.Control.Attempt.grid (retry_base fuel n trials time dt alpha grid)

theorem advance_base (fuel n trials : Nat) (time : UInt64) (grid : Array Cell) (acc : Vector) :
    (advance fuel n trials time grid acc).base =
      Project.EulerReconstructed.Control.advance fuel n trials time grid := by
  induction fuel generalizing time grid acc with
  | zero => rfl
  | succ fuel ih =>
    simp only [advance, Project.EulerReconstructed.Control.advance, retry_status, retry_dt, retry_grid]
    split
    · rfl
    · split
      · split
        · exact ih _ _ _
        · rfl
      · rfl

#print axioms attempt_eq
#print axioms retry_base
#print axioms advance_base
end Project.EulerCertificate.Control
