import Project.EulerRiemann.NumericsStepBalance
import Project.EulerRiemann.ControlTrace

namespace Project.EulerRiemann.Conservation
open Project.Euler2DCellStep.Sweep

noncomputable def traceSum {n : Nat} (term : UInt64 → Grid n n → Fin 4 → ℝ) :
    Grid n n → List UInt64 → Fin 4 → ℝ
  | _, [], _ => 0
  | grid, dt :: dts, i =>
      let ratio := Wasm.IEEE64.div dt (Time.spacing n)
      term ratio grid i + traceSum term (stepGrid ratio grid) dts i

theorem trace_balance {n : Nat} (hn : 0 < n) {time finalTime : UInt64}
    {grid finalGrid : Grid n n} {dts : List UInt64}
    (h : Control.NumericalTrace n time grid dts finalTime finalGrid) (i : Fin 4) :
    gridTotal hn finalGrid i - gridTotal hn grid i =
      traceSum (stepBoundary hn) grid dts i + traceSum (stepResidual hn) grid dts i := by
  induction h with
  | nil => simp [traceSum]
  | cons _ hs _ ih =>
    have he := (accepted_step_parts _ _ _ hs).2.2
    have hb := accepted_step_balance hn _ _ _ hs i
    rw [he] at ih hb
    simp only [traceSum]
    linarith only [hb, ih]

theorem trace_residual_bound {n : Nat} (hn : 0 < n) {time finalTime : UInt64}
    {grid finalGrid : Grid n n} {dts : List UInt64}
    (h : Control.NumericalTrace n time grid dts finalTime finalGrid) (i : Fin 4) :
    |traceSum (stepResidual hn) grid dts i| ≤ traceSum (stepErrorBound hn) grid dts i := by
  induction h with
  | nil => simp [traceSum]
  | cons _ hs _ ih =>
    have he := (accepted_step_parts _ _ _ hs).2.2
    rw [he] at ih
    exact le_trans (abs_add_le _ _)
      (add_le_add (accepted_step_residual_bound hn _ _ _ hs i) ih)

noncomputable def RunBalance (n : Nat) (hn : 0 < n) : Prop :=
  ∃ dts, Control.NumericalTrace n 0 (Initial.initial n) dts (Control.run n).time
      (Traversal.asGrid n (Control.run n).grid) ∧
    ∀ i : Fin 4,
      gridTotal hn (Traversal.asGrid n (Control.run n).grid) i - gridTotal hn (Initial.initial n) i =
        traceSum (stepBoundary hn) (Initial.initial n) dts i +
          traceSum (stepResidual hn) (Initial.initial n) dts i ∧
      |traceSum (stepResidual hn) (Initial.initial n) dts i| ≤
        traceSum (stepErrorBound hn) (Initial.initial n) dts i

theorem run_balance (n : Nat) (hn : 0 < n) (hsize : 2 ≤ n ∧ n ≤ 800) : RunBalance n hn := by
  obtain ⟨dts, ht, _⟩ := Control.run_trace n hsize
  exact ⟨dts, ht, fun i => ⟨trace_balance hn ht i, trace_residual_bound hn ht i⟩⟩

#print axioms trace_balance
#print axioms trace_residual_bound
#print axioms run_balance
end Project.EulerRiemann.Conservation
