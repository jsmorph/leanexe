import Project.EulerReconstructed.FrozenPhysicalStep

namespace Project.EulerReconstructed.Frozen.Conservation
open Project.EulerRiemann.Frozen.Traversal (Cell Indexed initialCells initialCells_indexed)

theorem physical_trace_balance {n trials : Nat} (hn : 0 < n) {time finalTime : UInt64}
    {grid finalGrid : Array Cell} {dts : List UInt64}
    (h : Control.NumericalTrace n trials time grid dts finalTime finalGrid)
    (hg : Indexed n grid) (i : Fin 4) :
    physicalTotal hn finalGrid i - physicalTotal hn grid i =
      durationSum n trials (stepPhysicalBoundary hn trials) grid dts i +
        durationSum n trials (stepPhysicalResidual hn trials) grid dts i := by
  induction h with
  | nil => simp [durationSum]
  | @cons time grid dt next dts finalTime finalGrid ht hs tail ih =>
    have he : next = Traversal.step n trials (traceRatio n dt grid) grid := hs.2.2.2
    have ha := hs.2.2.1
    rw [he] at ha
    have hnxt := Traversal.step_indexed n trials (traceRatio n dt grid) grid hg
    rw [← he] at hnxt
    have ih := ih hnxt
    have hb := step_physical_balance hn trials dt grid hg ha i
    rw [← he] at hb
    simp only [durationSum]
    rw [← he]
    linarith only [hb, ih]

theorem physical_trace_residual_bound {n trials : Nat} (hn : 0 < n) {time finalTime : UInt64}
    {grid finalGrid : Array Cell} {dts : List UInt64}
    (h : Control.NumericalTrace n trials time grid dts finalTime finalGrid)
    (hg : Indexed n grid) (i : Fin 4) :
    |durationSum n trials (stepPhysicalResidual hn trials) grid dts i| ≤
      durationSum n trials (stepPhysicalErrorBound hn trials) grid dts i := by
  induction h with
  | nil => simp [durationSum]
  | @cons time grid dt next dts finalTime finalGrid ht hs tail ih =>
    have he : next = Traversal.step n trials (traceRatio n dt grid) grid := hs.2.2.2
    have ha := hs.2.2.1
    rw [he] at ha
    have hnxt := Traversal.step_indexed n trials (traceRatio n dt grid) grid hg
    rw [← he] at hnxt
    have ih := ih hnxt
    simp only [durationSum]
    rw [← he]
    exact (abs_add_le _ _).trans (add_le_add
      (step_physical_residual_bound hn trials dt grid hg hs.2.1 ha i) ih)

noncomputable def PhysicalRunBalance (n trials : Nat) (hn : 0 < n) : Prop :=
  ∃ dts, Control.NumericalTrace n trials 0 (initialCells n) dts
      (Control.run n trials).time (Control.run n trials).grid ∧
    ∀ i : Fin 4,
      physicalTotal hn (Control.run n trials).grid i - physicalTotal hn (initialCells n) i =
        durationSum n trials (stepPhysicalBoundary hn trials) (initialCells n) dts i +
          durationSum n trials (stepPhysicalResidual hn trials) (initialCells n) dts i ∧
      |durationSum n trials (stepPhysicalResidual hn trials) (initialCells n) dts i| ≤
        durationSum n trials (stepPhysicalErrorBound hn trials) (initialCells n) dts i

theorem physical_run_balance (n trials : Nat) (hn : 0 < n) (hsize : 2 ≤ n ∧ n ≤ 800) :
    PhysicalRunBalance n trials hn := by
  obtain ⟨dts, ht, _⟩ := Control.run_trace n trials hsize
  exact ⟨dts, ht, fun i => ⟨physical_trace_balance hn ht (initialCells_indexed n hsize) i,
    physical_trace_residual_bound hn ht (initialCells_indexed n hsize) i⟩⟩

#print axioms physical_trace_balance
#print axioms physical_trace_residual_bound
#print axioms physical_run_balance
end Project.EulerReconstructed.Frozen.Conservation
