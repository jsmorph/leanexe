import Project.EulerRiemann.NumericsPhysicalStep
import Project.EulerRiemann.NumericsTraceBalance

namespace Project.EulerRiemann.Conservation
open Project.Euler2DCellStep.Sweep

theorem physical_trace_balance {n : Nat} (hn : 0 < n) {time finalTime : UInt64}
    {grid finalGrid : Grid n n} {dts : List UInt64}
    (h : Control.NumericalTrace n time grid dts finalTime finalGrid) (i : Fin 4) :
    physicalTotal hn finalGrid i - physicalTotal hn grid i =
      durationSum (stepPhysicalBoundary hn) grid dts i +
        durationSum (stepPhysicalResidual hn) grid dts i := by
  induction h with
  | nil => simp [durationSum]
  | cons _ hs _ ih =>
    have he := (accepted_step_parts _ _ _ hs).2.2
    have hb := step_physical_balance hn _ _ _ hs i
    rw [he] at ih hb
    simp only [durationSum]
    linarith only [hb, ih]

theorem physical_trace_residual_bound {n : Nat} (hn : 0 < n) (hsize : 2 ≤ n ∧ n ≤ 800)
    {time finalTime : UInt64} {grid finalGrid : Grid n n} {dts : List UInt64}
    (h : Control.NumericalTrace n time grid dts finalTime finalGrid) (i : Fin 4) :
    |durationSum (stepPhysicalResidual hn) grid dts i| ≤
      durationSum (stepPhysicalErrorBound hn) grid dts i := by
  induction h with
  | nil => simp [durationSum]
  | cons ht hs _ ih =>
    have he := (accepted_step_parts _ _ _ hs).2.2
    rw [he] at ih
    exact le_trans (abs_add_le _ _) (add_le_add
      (step_physical_residual_bound hn hsize _ _ _ _ ht hs i) ih)

noncomputable def PhysicalRunBalance (n : Nat) (hn : 0 < n) : Prop :=
  ∃ dts, Control.NumericalTrace n 0 (Initial.initial n) dts (Control.run n).time
      (Traversal.asGrid n (Control.run n).grid) ∧
    ∀ i : Fin 4,
      physicalTotal hn (Traversal.asGrid n (Control.run n).grid) i -
        physicalTotal hn (Initial.initial n) i =
        durationSum (stepPhysicalBoundary hn) (Initial.initial n) dts i +
          durationSum (stepPhysicalResidual hn) (Initial.initial n) dts i ∧
      |durationSum (stepPhysicalResidual hn) (Initial.initial n) dts i| ≤
        durationSum (stepPhysicalErrorBound hn) (Initial.initial n) dts i

theorem physical_run_balance (n : Nat) (hn : 0 < n) (hsize : 2 ≤ n ∧ n ≤ 800) :
    PhysicalRunBalance n hn := by
  obtain ⟨dts, ht, _⟩ := Control.run_trace n hsize
  exact ⟨dts, ht, fun i =>
    ⟨physical_trace_balance hn ht i, physical_trace_residual_bound hn hsize ht i⟩⟩

#print axioms physical_trace_balance
#print axioms physical_trace_residual_bound
#print axioms physical_run_balance
end Project.EulerRiemann.Conservation
