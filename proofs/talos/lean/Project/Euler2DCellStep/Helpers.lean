import Project.Euler2DCellStep.Program
import Project.Euler2DCellStep.Model
import Project.Euler2DDynamicFlux.Execution
import Project.EulerCellStep.Update

namespace Project.Euler2DCellStep.Execution
open Wasm Project.FunctionRegion
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

structure Layout (m : Wasm.Module) extends Project.Euler2DDynamicFlux.Execution.Layout m where
  update : m.funcs[28]? = some func28Def
  rejectedCell : m.funcs[34]? = some func34Def
  cell : m.funcs[35]? = some func35Def

theorem concreteLayout : Layout Project.Euler2DCellStep.«module» :=
  ⟨⟨⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

def updateDomain (index : Nat) : Prop :=
  index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 8 ∨ index = 19

def updateRename (index : Nat) : Nat :=
  if index = 19 then 28 else if index < 3 then index else index + 8

theorem updateShift {m : Wasm.Module} (layout : Layout m) :
    Shift Project.EulerCellStep.«module» m updateRename updateRename updateDomain := by
  refine ⟨rfl, layout.noImports, layout.memory, ?_⟩
  intro index h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · refine ⟨Project.EulerCellStep.func0Def, rfl, layout.positive, ?_⟩
    prove_portable
  · refine ⟨Project.EulerCellStep.func1Def, rfl, layout.abs, ?_⟩
    prove_portable
  · refine ⟨Project.EulerCellStep.func2Def, rfl, layout.finite, ?_⟩
    prove_portable
    all_goals simp [updateDomain]
  · refine ⟨Project.EulerCellStep.func8Def, rfl, layout.rejectedComponent, ?_⟩
    prove_portable
  · refine ⟨Project.EulerCellStep.func19Def, rfl, layout.update, ?_⟩
    prove_portable
    all_goals simp [updateDomain]

theorem updateCheckedBits_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio state fluxL fluxR : UInt64) :
    TerminatesWith env m 28 initial [.i64 fluxR, .i64 fluxL, .i64 state, .i64 ratio]
      (fun final values => final = initial ∧
        values = Project.EulerCellStep.Execution.updateValues ratio state fluxL fluxR) :=
  Project.FunctionRegion.terminatesWith (updateShift layout) 19 (by simp [updateDomain])
    (Project.EulerCellStep.Execution.updateCheckedBits_exact_in_module
      Project.EulerCellStep.Execution.concreteLayout env initial ratio state fluxL fluxR)

theorem rejectedCell_exact {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env m 34 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func34Def)
    (by simpa [layout.noImports] using layout.rejectedCell) ?_ (by simp [layout.noImports])
  change wp m func34 _ initial (func34Def.toLocals []) env
  unfold func34
  wp_run
  simp [func34Def, List.set]

#print axioms concreteLayout
#print axioms updateShift
#print axioms updateCheckedBits_exact_in_module
#print axioms rejectedCell_exact
end Project.Euler2DCellStep.Execution
