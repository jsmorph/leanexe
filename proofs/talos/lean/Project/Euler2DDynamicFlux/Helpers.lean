import Project.Euler2DDynamicFlux.Program
import Project.Euler2DDynamicFlux.Model
import Project.Euler2DConservative.Execution
import Project.EulerDynamicFlux.Component

namespace Project.Euler2DDynamicFlux.Execution
open Wasm
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

structure Layout (m : Wasm.Module) extends Project.Euler2DConservative.Execution.HelperLayout m where
  side : m.funcs[5]? = some Project.Euler2DConservative.func5Def
  rejectedComponent : m.funcs[8]? = some Project.EulerDynamicFlux.func8Def
  component : m.funcs[9]? = some Project.EulerDynamicFlux.func9Def
  rejectedFlux : m.funcs[16]? = some func16Def
  flux : m.funcs[17]? = some func17Def

def Layout.components {m : Wasm.Module} (layout : Layout m) :
    Project.EulerDynamicFlux.Execution.ComponentLayout m :=
  ⟨layout.toHelperLayout.toScalarLayout, layout.rejectedComponent, layout.component⟩

theorem concreteLayout : Layout Project.Euler2DDynamicFlux.«module» :=
  ⟨⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem rejectedFlux_exact {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env m 16 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func16Def)
    (by simpa [layout.noImports] using layout.rejectedFlux) ?_ (by simp [layout.noImports])
  change wp m func16 _ initial (func16Def.toLocals []) env
  unfold func16
  wp_run
  simp [func16Def, List.set]

#print axioms concreteLayout
#print axioms rejectedFlux_exact
end Project.Euler2DDynamicFlux.Execution
