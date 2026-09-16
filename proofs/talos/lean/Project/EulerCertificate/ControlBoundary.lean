import Project.EulerCertificate.ControlProjection
import Project.EulerCertificate.BoundaryStep

namespace Project.EulerCertificate.Control
open Project.EulerRiemann
open Project.EulerRiemann.Traversal (Cell Indexed accepted)
open Project.EulerReconstructed.Conservation (traceRatio stepPhysicalBoundary)

theorem retry_success (fuel n trials : Nat) (time dt alpha : UInt64) (grid : Array Cell)
    (h : (retry fuel n trials time dt alpha grid).status = 0) :
    let out := retry fuel n trials time dt alpha grid
    Time.validAdvance time out.dt = true ∧
      (OutwardCfl.gridRatioChecked n out.dt alpha).status = 0 ∧
      accepted out.grid = true ∧
      out.grid = Project.EulerReconstructed.Traversal.step n trials
        (OutwardCfl.gridRatioChecked n out.dt alpha).value grid := by
  rw [retry_status] at h
  simpa only [retry_dt, retry_grid] using
    Project.EulerReconstructed.Control.retry_success fuel n trials time dt alpha grid h

theorem retry_boundary (fuel n trials : Nat) (time dt alpha : UInt64) (grid : Array Cell)
    (h : (retry fuel n trials time dt alpha grid).status = 0) :
    let out := retry fuel n trials time dt alpha grid
    out.boundary = Boundary.physicalStep n trials out.dt grid
      (Project.EulerReconstructed.Traversal.sweep n trials false
        (OutwardCfl.gridRatioChecked n out.dt alpha).value grid) := by
  revert h
  induction fuel generalizing dt with
  | zero => simp [retry]
  | succ fuel ih =>
    simp only [retry, attempt_eq]
    split
    · split
      · by_cases ha : accepted (Project.EulerReconstructed.Traversal.step n trials
            (OutwardCfl.gridRatioChecked n dt alpha).value grid) = true
        · simp [ha]
        · simp only [ha]
          exact ih _
      · exact ih _
    · simp

theorem retry_valid {n : Nat} (hn : 0 < n) (hmax : n ≤ 800) (fuel trials : Nat)
    (time dt : UInt64) (grid : Array Cell) (hg : Indexed n grid)
    (h : (retry fuel n trials time dt (OutwardMaximum.gridUpper grid).value grid).status = 0) :
    let out := retry fuel n trials time dt (OutwardMaximum.gridUpper grid).value grid
    Vectors.Valid out.boundary (stepPhysicalBoundary hn trials out.dt grid) := by
  dsimp only
  rw [retry_boundary fuel n trials time dt (OutwardMaximum.gridUpper grid).value grid h]
  exact Boundary.physicalStep_encloses_trace hn hmax trials _ grid hg

#print axioms retry_success
#print axioms retry_boundary
#print axioms retry_valid
end Project.EulerCertificate.Control
