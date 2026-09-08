import Project.EulerGridStep.Program
import Project.EulerGridStep.Outputs
import Project.EulerCellStep.Execution
import Project.Runtime.Defs
import Project.ProofKit.Array

namespace Project.EulerGridStep.Execution
open Wasm

/-- The complete scalar checked-cell proof applies unchanged inside this grid module. -/
theorem cellLayout : Project.EulerCellStep.Execution.Layout Project.EulerGridStep.«module» := by
  exact ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- Exact call boundaries for the copying writer, cell iteration and grid entry. -/
structure Layout (m : Wasm.Module) extends toCellLayout : Project.EulerCellStep.Execution.Layout m where
  writeField : m.funcs[27]? = some func27Def
  writeCell : m.funcs[34]? = some func34Def
  advance : m.funcs[35]? = some func35Def
  step : m.funcs[36]? = some func36Def
  release : m.funcs[40]? = some { Project.Runtime.releaseFuncDef 40 with typeIdx := some 40 }
  memory32 : m.memIs64 = false

theorem concreteLayout : Layout Project.EulerGridStep.«module» := by
  exact ⟨cellLayout, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms cellLayout
#print axioms concreteLayout
end Project.EulerGridStep.Execution
