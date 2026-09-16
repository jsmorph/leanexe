import Project.EulerCertificate.SolveSpec
import Project.ProofKit.F64IntervalBounds

namespace Project.EulerCertificate.Solve
open Project.EulerRiemann.Traversal (initialCells)
open Project.EulerReconstructed.Control (NumericalTrace)
open Project.EulerReconstructed.Conservation
open CodeLib.IEEE64 (value)

theorem run_absolute_bound (n trials : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    ∃ dts, NumericalTrace n trials 0 (initialCells n) dts (run n trials).time (run n trials).grid ∧
      ∀ i : Fin 4, (Flux.get (run n trials).residual i).status = 0 →
        |durationSum n trials (stepPhysicalResidual (by omega : 0 < n) trials) (initialCells n) dts i| ≤
          max (-value (Flux.get (run n trials).residual i).lower)
            (value (Flux.get (run n trials).residual i).upper) := by
  obtain ⟨dts, ht, hv⟩ := run_enclosure n trials hn
  exact ⟨dts, ht, fun i hi => (hv i).absolute_bound hi⟩

#print axioms run_absolute_bound
end Project.EulerCertificate.Solve
