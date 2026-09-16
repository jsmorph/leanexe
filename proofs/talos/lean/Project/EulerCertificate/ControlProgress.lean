import Project.EulerCertificate.ControlProjection
import Project.EulerReconstructed.ControlRetry

namespace Project.EulerCertificate.Control
open Project.EulerRiemann
open Project.EulerRiemann.Traversal (Cell Indexed)

theorem retry_valid (fuel n trials : Nat) (time dt alpha : UInt64) (grid : Array Cell)
    (h : (retry fuel n trials time dt alpha grid).status = 0) :
    Time.validAdvance time (retry fuel n trials time dt alpha grid).dt = true := by
  rw [retry_dt]
  exact (Project.EulerReconstructed.Control.retry_success fuel n trials time dt alpha grid
    (by simpa only [retry_status] using h)).1

theorem retry_indexed (fuel n trials : Nat) (time dt alpha : UInt64) (grid : Array Cell)
    (hg : Indexed n grid) (h : (retry fuel n trials time dt alpha grid).status = 0) :
    Indexed n (retry fuel n trials time dt alpha grid).grid := by
  rw [retry_grid]
  exact Project.EulerReconstructed.Control.retry_indexed fuel n trials time dt alpha grid hg
    (by simpa only [retry_status] using h)

#print axioms retry_valid
#print axioms retry_indexed
end Project.EulerCertificate.Control
