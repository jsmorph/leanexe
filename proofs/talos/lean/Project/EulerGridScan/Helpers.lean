import Project.EulerGridScan.Program
import Project.EulerConservative.Execution
import Project.EulerGridStep.Scan
import Project.ProofKit.Array

namespace Project.EulerGridScan.Execution

structure Layout (m : Wasm.Module) : Prop extends Project.EulerConservative.Execution.HelperLayout m where
  side : m.funcs[5]? = some Project.EulerConservative.func5Def
  scanAt : m.funcs[8]? = some func8Def
  scan : m.funcs[11]? = some func11Def

theorem concreteLayout : Layout Project.EulerGridScan.«module» := by
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- One checked-cell speed-fold iteration, preserving the model's IEEE words. -/
def iterationValues (input : Array UInt64) (index : Nat) (speed : UInt64) : List Wasm.Value :=
  let result := Project.EulerGridStep.Model.scan input index speed 1
  [.i64 result.speed, .i64 result.status]

#print axioms concreteLayout
end Project.EulerGridScan.Execution
