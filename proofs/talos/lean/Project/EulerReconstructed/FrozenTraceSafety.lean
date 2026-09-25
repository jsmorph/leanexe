import Project.EulerReconstructed.FrozenNumericalSafety
import Project.EulerReconstructed.FrozenTraceBalance
import Project.EulerReconstructed.FrozenControlTrace
import Project.EulerRiemann.FrozenOutwardMaximumCfl

namespace Project.EulerReconstructed.Frozen.Numerics
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (orient)
open Project.EulerRiemann.Frozen.Traversal (Cell accepted initialCells initialCells_getElem initialCell_safe)
open Project.EulerRiemann.Frozen.Control (CellsSafe)
open Project.EulerRiemann.Frozen.Hyperbolicity (CellsHyperbolic cells_hyperbolic)
open Conservation (traceRatio)

noncomputable def StepFacts (n fuel : Nat) (dt : UInt64) (grid next : Array Cell) : Prop :=
  CellsHyperbolic next ∧
    (∀ cell ∈ grid, ∀ axis i, value dt * (n : ℝ) * characteristicMagnitude (orient axis cell.state) i ≤ 1/2) ∧
    SweepFacts n fuel dt (Conservation.traceRatio n dt grid) false grid ∧
    SweepFacts n fuel dt (Conservation.traceRatio n dt grid) true
      (Traversal.sweep n fuel false (Conservation.traceRatio n dt grid) grid)

theorem step_facts (n fuel : Nat) (dt : UInt64) (grid next : Array Cell)
    (h : Control.AcceptedStep n fuel dt grid next) : StepFacts n fuel dt grid next := by
  have he : next = Traversal.step n fuel (Conservation.traceRatio n dt grid) grid := h.2.2.2
  have ha := h.2.2.1
  rw [he] at ha
  obtain ⟨hx, hy, _⟩ := Conservation.accepted_step_parts n fuel _ grid ha
  have hr : value dt * (n : ℝ) ≤ value (Conservation.traceRatio n dt grid) :=
    (Project.EulerRiemann.Frozen.OutwardCfl.grid_ratio_accepted n dt _ h.2.1).2.2.2.2.2.1
  refine ⟨?_, ?_, sweep_facts n fuel dt _ false grid hr hx,
    sweep_facts n fuel dt _ true _ hr hy⟩
  · rw [he]
    exact cells_hyperbolic _ (Traversal.step_safe n fuel _ grid ha)
  · intro cell hc axis i
    exact Project.EulerRiemann.Frozen.OutwardMaximum.grid_characteristic_courant grid n dt h.1 h.2.1 cell hc axis i

theorem trace_safe {n fuel : Nat} {time finalTime : UInt64}
    {grid finalGrid : Array Cell} {dts : List UInt64}
    (ht : Control.NumericalTrace n fuel time grid dts finalTime finalGrid)
    (hs : CellsSafe grid) : CellsSafe finalGrid := by
  induction ht with
  | nil => exact hs
  | cons _ hstep _ ih =>
    apply ih
    have he := hstep.2.2.2
    have ha := hstep.2.2.1
    rw [he] at ha ⊢
    exact Traversal.step_safe n fuel _ _ ha

noncomputable def TraceFacts (n fuel : Nat) : Prop :=
  ∀ time grid dts, Control.NumericalTrace n fuel 0 (initialCells n) dts time grid →
    CellsHyperbolic grid ∧ ∀ dt next, Control.AcceptedStep n fuel dt grid next →
      StepFacts n fuel dt grid next

theorem initial_trace_facts (n fuel : Nat) (hn : 2 ≤ n ∧ n ≤ 800) : TraceFacts n fuel := by
  intro time grid dts ht
  have hInitial : CellsSafe (initialCells n) := by
    intro i hi
    rw [initialCells_getElem n hn i hi]
    exact initialCell_safe n i
  exact ⟨cells_hyperbolic _ (trace_safe ht hInitial), fun dt next hs => step_facts n fuel dt grid next hs⟩

#print axioms step_facts
#print axioms trace_safe
#print axioms initial_trace_facts
end Project.EulerReconstructed.Frozen.Numerics
