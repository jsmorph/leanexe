import Project.FunctionRegion.Exec
import Project.ClobLimit.Program
import Project.ClobMarket.Program

/-!
# Reused export-helper region

The market and limit artifacts share the validity subsystem and both status
helpers at the same indices.  This domain contains their complete direct-call
closure.  Semantic transport therefore reuses their completed specifications.
-/

namespace Project.ClobMarket.ExportRegion

open Project.FunctionRegion

def ExportDomain (id : Nat) : Prop :=
  id = 2 ∨ id = 5 ∨ id = 6 ∨ id = 19 ∨ id = 20

set_option maxRecDepth 1048576 in
theorem exportShift : Shift Project.ClobLimit.«module»
    Project.ClobMarket.«module» id ExportDomain := by
  refine
    { sourceImports := rfl
      targetImports := rfl
      memory := rfl
      functions := ?_ }
  intro functionId hDomain
  rcases hDomain with rfl | rfl | rfl | rfl | rfl
  · refine ⟨Project.ClobLimit.func2Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobLimit.func5Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobLimit.func6Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [ExportDomain]
  · refine ⟨Project.ClobLimit.func19Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobLimit.func20Def, rfl, rfl, ?_⟩
    prove_portable

end Project.ClobMarket.ExportRegion
