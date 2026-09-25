import Project.EulerReconstructed.FrozenStepBalance
import Project.EulerReconstructed.FrozenControlTrace

namespace Project.EulerReconstructed.Frozen.Conservation
open Project.EulerRiemann.Frozen.Traversal (Cell Indexed asGrid initialCells initialCells_indexed)
open Project.EulerRiemann.Frozen.Conservation (gridTotal)

def traceRatio (n : Nat) (dt : UInt64) (grid : Array Cell) : UInt64 :=
  (Project.EulerRiemann.Frozen.OutwardCfl.gridRatioChecked n dt
    (Project.EulerRiemann.Frozen.OutwardMaximum.gridUpper grid).value).value

noncomputable def durationSum (n trials : Nat) (term : UInt64 → Array Cell → Fin 4 → ℝ) :
    Array Cell → List UInt64 → Fin 4 → ℝ
  | _, [], _ => 0
  | grid, dt :: dts, i =>
      term dt grid i + durationSum n trials term
        (Traversal.step n trials (traceRatio n dt grid) grid) dts i

noncomputable def traceSum (n trials : Nat) (term : UInt64 → Array Cell → Fin 4 → ℝ)
    (grid : Array Cell) (dts : List UInt64) (i : Fin 4) : ℝ :=
  durationSum n trials (fun dt grid => term (traceRatio n dt grid) grid) grid dts i

theorem trace_balance {n trials : Nat} (hn : 0 < n) {time finalTime : UInt64}
    {grid finalGrid : Array Cell} {dts : List UInt64}
    (h : Control.NumericalTrace n trials time grid dts finalTime finalGrid)
    (hg : Indexed n grid) (i : Fin 4) :
    gridTotal hn (asGrid n finalGrid) i - gridTotal hn (asGrid n grid) i =
      traceSum n trials (stepBoundary hn trials) grid dts i +
        traceSum n trials (stepResidual hn trials) grid dts i := by
  induction h with
  | nil => simp [traceSum, durationSum]
  | @cons time grid dt next dts finalTime finalGrid ht hs tail ih =>
    have he : next = Traversal.step n trials (traceRatio n dt grid) grid := hs.2.2.2
    have ha := hs.2.2.1
    rw [he] at ha
    have hnxt := Traversal.step_indexed n trials (traceRatio n dt grid) grid hg
    rw [← he] at hnxt
    have ih := ih hnxt
    have hb := accepted_step_balance hn trials (traceRatio n dt grid) grid hg ha i
    rw [← he] at hb
    simp only [traceSum, durationSum] at ih ⊢
    rw [← he]
    linarith only [hb, ih]

theorem trace_residual_bound {n trials : Nat} (hn : 0 < n) {time finalTime : UInt64}
    {grid finalGrid : Array Cell} {dts : List UInt64}
    (h : Control.NumericalTrace n trials time grid dts finalTime finalGrid)
    (hg : Indexed n grid) (i : Fin 4) :
    |traceSum n trials (stepResidual hn trials) grid dts i| ≤
      traceSum n trials (stepErrorBound hn trials) grid dts i := by
  induction h with
  | nil => simp [traceSum, durationSum]
  | @cons time grid dt next dts finalTime finalGrid ht hs tail ih =>
    have he : next = Traversal.step n trials (traceRatio n dt grid) grid := hs.2.2.2
    have ha := hs.2.2.1
    rw [he] at ha
    have hnxt := Traversal.step_indexed n trials (traceRatio n dt grid) grid hg
    rw [← he] at hnxt
    have ih := ih hnxt
    simp only [traceSum, durationSum]
    rw [← he]
    exact (abs_add_le _ _).trans (add_le_add
      (accepted_step_residual_bound hn trials (traceRatio n dt grid) grid hg ha i) ih)

noncomputable def RunBalance (n trials : Nat) (hn : 0 < n) : Prop :=
  ∃ dts, Control.NumericalTrace n trials 0 (initialCells n) dts
      (Control.run n trials).time (Control.run n trials).grid ∧
    ∀ i : Fin 4,
      gridTotal hn (asGrid n (Control.run n trials).grid) i - gridTotal hn (asGrid n (initialCells n)) i =
        traceSum n trials (stepBoundary hn trials) (initialCells n) dts i +
          traceSum n trials (stepResidual hn trials) (initialCells n) dts i ∧
      |traceSum n trials (stepResidual hn trials) (initialCells n) dts i| ≤
        traceSum n trials (stepErrorBound hn trials) (initialCells n) dts i

theorem run_balance (n trials : Nat) (hn : 0 < n) (hsize : 2 ≤ n ∧ n ≤ 800) :
    RunBalance n trials hn := by
  obtain ⟨dts, ht, _⟩ := Control.run_trace n trials hsize
  exact ⟨dts, ht, fun i => ⟨trace_balance hn ht (initialCells_indexed n hsize) i,
    trace_residual_bound hn ht (initialCells_indexed n hsize) i⟩⟩

#print axioms trace_balance
#print axioms trace_residual_bound
#print axioms run_balance
end Project.EulerReconstructed.Frozen.Conservation
