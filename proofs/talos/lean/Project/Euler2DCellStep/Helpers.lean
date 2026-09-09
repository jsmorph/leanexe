import Project.Euler2DCellStep.Program
import Project.Euler2DCellStep.Model
import Project.Euler2DDynamicFlux.Execution
import Project.EulerCellStep.Update

namespace Project.Euler2DCellStep.Execution
open Wasm
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

structure Layout (m : Wasm.Module) extends Project.Euler2DDynamicFlux.Execution.Layout m where
  update : m.funcs[20]? = some { Project.EulerCellStep.func19Def with typeIdx := some 20 }
  rejectedCell : m.funcs[26]? = some func26Def
  cell : m.funcs[27]? = some func27Def

theorem concreteLayout : Layout Project.Euler2DCellStep.«module» :=
  ⟨⟨⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem updateCheckedBits_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio state fluxL fluxR : UInt64) :
    TerminatesWith env m 20 initial [.i64 fluxR, .i64 fluxL, .i64 state, .i64 ratio]
      (fun final values => final = initial ∧
        values = Project.EulerCellStep.Execution.updateValues ratio state fluxL fluxR) :=
  Project.EulerCellStep.Execution.updateCheckedBits_exact_in_module_core
    layout.toLayout.components 20 (some 20) layout.update env initial ratio state fluxL fluxR

theorem rejectedCell_exact {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env m 26 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func26Def)
    (by simpa [layout.noImports] using layout.rejectedCell) ?_ (by simp [layout.noImports])
  change wp m func26 _ initial (func26Def.toLocals []) env
  unfold func26
  wp_run
  simp [func26Def, List.set]

#print axioms concreteLayout
#print axioms updateCheckedBits_exact_in_module
#print axioms rejectedCell_exact
end Project.Euler2DCellStep.Execution
