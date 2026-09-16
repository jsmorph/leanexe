import Project.EulerCertificate.BoundarySum
import Project.EulerReconstructed.PhysicalStep
import Project.EulerRiemann.TimeBounds

namespace Project.EulerCertificate.Boundary
open Project.EulerRiemann.Traversal (Cell Indexed asGrid)
open Project.EulerReconstructed.Conservation
open CodeLib.IEEE64 (value)

theorem physicalStep_valid {n : Nat} (hn : 0 < n) (hmax : n ≤ 800)
    (trials : Nat) (dt : UInt64) (grid middle : Array Cell)
    (hg : Indexed n grid) (hm : Indexed n middle) :
    Vectors.Valid (physicalStep n trials dt grid middle) (fun i =>
      value dt / (n : ℝ) * (gridReferenceFlux hn trials false (asGrid n grid) i +
        gridReferenceFlux hn trials true (asGrid n middle) i)) := by
  have h := (((sum_valid hn trials false grid hg).add
    (sum_valid hn trials true middle hm)).scale dt).divPositive
      (Project.EulerRiemann.Time.smallNaturalBits n)
  rw [Project.EulerRiemann.Time.smallNaturalBits_value n hmax] at h
  have he : ∀ a b c d : ℝ, (a + b) * c / d = c / d * (a + b) := by intros; ring
  simpa only [physicalStep, he] using h

theorem physicalStep_encloses_trace {n : Nat} (hn : 0 < n) (hmax : n ≤ 800)
    (trials : Nat) (dt : UInt64) (grid : Array Cell) (hg : Indexed n grid) :
    Vectors.Valid (physicalStep n trials dt grid
      (Project.EulerReconstructed.Traversal.sweep n trials false (traceRatio n dt grid) grid))
      (stepPhysicalBoundary hn trials dt grid) :=
  physicalStep_valid hn hmax trials dt grid _ hg
    (Project.EulerReconstructed.Traversal.sweep_indexed n trials false (traceRatio n dt grid) grid hg)

#print axioms physicalStep_valid
#print axioms physicalStep_encloses_trace
end Project.EulerCertificate.Boundary
