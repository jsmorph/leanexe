import Project.Euler2DDynamicFlux.Program
import Project.Euler2DDynamicFlux.Model
import Project.Euler2DConservative.Execution
import Project.EulerDynamicFlux.Component
import Project.FunctionRegion.Exec

namespace Project.Euler2DDynamicFlux.Execution
open Wasm Project.FunctionRegion
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

structure Layout (m : Wasm.Module) extends Project.Euler2DConservative.Execution.HelperLayout m where
  memory : Project.EulerDynamicFlux.«module».memory = m.memory
  side : m.funcs[13]? = some Project.Euler2DConservative.func13Def
  rejectedComponent : m.funcs[16]? = some func16Def
  component : m.funcs[17]? = some func17Def
  rejectedFlux : m.funcs[24]? = some func24Def
  flux : m.funcs[25]? = some func25Def

theorem concreteLayout : Layout Project.Euler2DDynamicFlux.«module» :=
  ⟨⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

def componentDomain (index : Nat) : Prop :=
  index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 8 ∨ index = 9

def componentRename (index : Nat) : Nat := if index < 3 then index else index + 8

theorem componentShift {m : Wasm.Module} (layout : Layout m) :
    Shift Project.EulerDynamicFlux.«module» m componentRename componentRename componentDomain := by
  refine ⟨rfl, layout.noImports, layout.memory, ?_⟩
  intro index h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · refine ⟨Project.EulerDynamicFlux.func0Def, rfl, layout.positive, ?_⟩
    prove_portable
  · refine ⟨Project.EulerDynamicFlux.func1Def, rfl, layout.abs, ?_⟩
    prove_portable
  · refine ⟨Project.EulerDynamicFlux.func2Def, rfl, layout.finite, ?_⟩
    prove_portable
    all_goals simp [componentDomain]
  · refine ⟨Project.EulerDynamicFlux.func8Def, rfl, layout.rejectedComponent, ?_⟩
    prove_portable
  · refine ⟨Project.EulerDynamicFlux.func9Def, rfl, layout.component, ?_⟩
    prove_portable
    all_goals simp [componentDomain]

theorem componentCheckedBits_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (alpha fluxL fluxR stateL stateR : UInt64) :
    TerminatesWith env m 17 initial [.i64 stateR, .i64 stateL, .i64 fluxR, .i64 fluxL, .i64 alpha]
      (fun final values => final = initial ∧
        values = Project.EulerDynamicFlux.Execution.componentValues alpha fluxL fluxR stateL stateR) :=
  Project.FunctionRegion.terminatesWith (componentShift layout) 9 (by simp [componentDomain])
    (Project.EulerDynamicFlux.Execution.componentCheckedBits_exact_in_module
      Project.EulerDynamicFlux.Execution.concreteLayout env initial alpha fluxL fluxR stateL stateR)

theorem rejectedFlux_exact {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env m 24 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func24Def)
    (by simpa [layout.noImports] using layout.rejectedFlux) ?_ (by simp [layout.noImports])
  change wp m func24 _ initial (func24Def.toLocals []) env
  unfold func24
  wp_run
  simp [func24Def, List.set]

#print axioms concreteLayout
#print axioms componentShift
#print axioms componentCheckedBits_exact_in_module
#print axioms rejectedFlux_exact
end Project.Euler2DDynamicFlux.Execution
