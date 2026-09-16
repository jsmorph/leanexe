import Project.EulerCertificate.Solve
import Project.EulerCertificate.ControlTrace
import Project.EulerCertificate.TotalsGrid
import Project.EulerReconstructed.PhysicalTrace

namespace Project.EulerCertificate.Solve
open Project.EulerRiemann
open Project.EulerRiemann.Traversal (Cell Indexed initialCells initialCells_indexed)
open Project.EulerReconstructed.Control (NumericalTrace)
open Project.EulerReconstructed.Conservation

def Report.base (report : Report) : Project.EulerRiemann.Control.Result :=
  ⟨report.status, report.time, report.grid⟩

theorem run_base (n trials : Nat) :
    (run n trials).base = Project.EulerReconstructed.Control.run n trials := by
  simp only [run, Project.EulerReconstructed.Control.run]
  split
  · exact Control.advance_base _ _ _ _ _ _
  · rfl

theorem run_enclosure (n trials : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    ∃ dts, NumericalTrace n trials 0 (initialCells n) dts (run n trials).time (run n trials).grid ∧
      Vectors.Valid (run n trials).residual
        (durationSum n trials (stepPhysicalResidual (by omega : 0 < n) trials) (initialCells n) dts) := by
  have hpos : 0 < n := by omega
  have hg := initialCells_indexed n hn
  let out := Control.advance (Time.endTime.toNat + 1) n trials 0 (initialCells n) Vectors.zero
  obtain ⟨dts, ht, hb⟩ := Control.advance_trace hpos hn.2
    (Time.endTime.toNat + 1) trials 0 (initialCells n) Vectors.zero (fun _ => 0) hg Vectors.zero_valid
  have ho : Indexed n out.grid := by
    have he := congrArg Project.EulerRiemann.Control.Result.grid
      (Control.advance_base (Time.endTime.toNat + 1) n trials 0 (initialCells n) Vectors.zero)
    change out.grid = _ at he
    rw [he]
    exact Project.EulerReconstructed.Control.advance_indexed _ _ _ _ _ hg
  have hi := Totals.physical_encloses_grid hpos hn.2 (initialCells n) hg
  have hf := Totals.physical_encloses_grid hpos hn.2 out.grid ho
  have hv := (hf.sub hi).sub hb
  simp only [zero_add] at hv
  refine ⟨dts, ?_, ?_⟩
  · simpa only [run, hn, and_self, ite_true] using ht
  · simp only [run, hn, and_self, ite_true]
    intro i
    have balance := physical_trace_balance hpos ht hg i
    have he : physicalTotal hpos out.grid i - physicalTotal hpos (initialCells n) i -
        durationSum n trials (stepPhysicalBoundary hpos trials) (initialCells n) dts i =
        durationSum n trials (stepPhysicalResidual hpos trials) (initialCells n) dts i := by
      linarith only [balance]
    have hvi := hv i
    dsimp only at hvi
    rw [he] at hvi
    exact hvi

#print axioms run_base
#print axioms run_enclosure
end Project.EulerCertificate.Solve
