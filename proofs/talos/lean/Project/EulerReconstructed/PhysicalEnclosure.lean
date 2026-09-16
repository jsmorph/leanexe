import Project.EulerReconstructed.PhysicalTrace
import Project.ProofKit.RealBalanceEnclosure

namespace Project.EulerReconstructed.Conservation
open Project.EulerRiemann.Traversal (Cell Indexed)

theorem physical_trace_residual_enclosure {n trials : Nat} (hn : 0 < n)
    {time finalTime : UInt64} {grid finalGrid : Array Cell} {dts : List UInt64}
    (h : Control.NumericalTrace n trials time grid dts finalTime finalGrid)
    (hg : Indexed n grid) (i : Fin 4)
    (initialLo initialHi finalLo finalHi boundaryLo boundaryHi : ℝ)
    (hInitial : initialLo ≤ physicalTotal hn grid i ∧
      physicalTotal hn grid i ≤ initialHi)
    (hFinal : finalLo ≤ physicalTotal hn finalGrid i ∧
      physicalTotal hn finalGrid i ≤ finalHi)
    (hBoundary : boundaryLo ≤ durationSum n trials (stepPhysicalBoundary hn trials) grid dts i ∧
      durationSum n trials (stepPhysicalBoundary hn trials) grid dts i ≤ boundaryHi) :
    finalLo - initialHi - boundaryHi ≤
        durationSum n trials (stepPhysicalResidual hn trials) grid dts i ∧
      durationSum n trials (stepPhysicalResidual hn trials) grid dts i ≤
        finalHi - initialLo - boundaryLo :=
  Project.ProofKit.RealBalanceEnclosure.residual_bounds _ _ _ _ _ _ _ _ _ _
    (physical_trace_balance hn h hg i) hInitial hFinal hBoundary

#print axioms physical_trace_residual_enclosure
end Project.EulerReconstructed.Conservation
