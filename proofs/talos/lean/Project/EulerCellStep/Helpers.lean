import Project.EulerCellStep.Program
import Project.EulerCellStep.Model
import Project.EulerDynamicFlux.Execution

namespace Project.EulerCellStep.Execution
open Wasm
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- Preserve the proved dynamic interface and identify the new cell functions. -/
structure Layout (m : Wasm.Module) extends Project.EulerDynamicFlux.Execution.Layout m where
  update : m.funcs[19]? = some func19Def
  rejectedCell : m.funcs[24]? = some func24Def
  cell : m.funcs[25]? = some func25Def

theorem concreteLayout : Layout Project.EulerCellStep.«module» := by
  exact ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem rejectedCell_exact {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env m 24 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func24Def)
    (by simpa [layout.noImports] using layout.rejectedCell) ?_ (by simp [layout.noImports])
  change wp m func24 _ initial
    { params := [], locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0], values := [] } env
  unfold func24
  wp_run
  simp [func24Def]

#print axioms concreteLayout
#print axioms rejectedCell_exact
end Project.EulerCellStep.Execution
