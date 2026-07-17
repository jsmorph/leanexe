import Project.FunctionRegion.Exec
import Project.ClobLimit.Program
import Project.ClobMarket.Program

/-!
# Reused matching region

The market and limit artifacts contain the same closed function region for
`runMatch`.  The identity renaming covers its complete direct-call closure.
Semantic transport can therefore reuse the proved limit matcher behavior.
-/

namespace Project.ClobMarket.MatchRegion

open Project.FunctionRegion

def MatchDomain (id : Nat) : Prop :=
  id = 8 ∨ id = 10 ∨ id = 11 ∨ id = 13 ∨ id = 14 ∨ id = 17 ∨ id = 18

set_option maxRecDepth 1048576 in
theorem matchShift : Shift Project.ClobLimit.«module»
    Project.ClobMarket.«module» id MatchDomain := by
  refine
    { sourceImports := rfl
      targetImports := rfl
      memory := rfl
      functions := ?_ }
  intro functionId hDomain
  rcases hDomain with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨Project.ClobLimit.func8Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobLimit.func10Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobLimit.func11Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [MatchDomain]
  · refine ⟨Project.ClobLimit.func13Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [MatchDomain]
  · refine ⟨Project.ClobLimit.func14Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [MatchDomain]
  · refine ⟨Project.ClobLimit.func17Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [MatchDomain]
  · refine ⟨Project.ClobLimit.func18Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [MatchDomain]

end Project.ClobMarket.MatchRegion
