import Project.FunctionRegion.Exec
import Project.ClobLimit.FrozenProgram
import Project.ClobMarket.FrozenProgram

/-!
# Reused matching region

The market and limit artifacts contain the same closed function region for
`runMatch`.  The identity renaming covers its complete direct-call closure.
Semantic transport can therefore reuse the proved limit matcher behavior.
-/

namespace Project.ClobMarket.Frozen.MatchRegion

open Project.FunctionRegion

def MatchDomain (id : Nat) : Prop :=
  id = 8 ∨ id = 10 ∨ id = 11 ∨ id = 13 ∨ id = 14 ∨ id = 17 ∨ id = 18

set_option maxRecDepth 1048576 in
private theorem func17_portable :
    PortableProgram MatchDomain Project.ClobLimit.Frozen.func17 := by
  prove_portable
  all_goals simp [MatchDomain]

set_option maxRecDepth 1048576 in
private theorem func18_portable :
    PortableProgram MatchDomain Project.ClobLimit.Frozen.func18 := by
  prove_portable
  all_goals simp [MatchDomain]

set_option maxRecDepth 1048576 in
theorem matchShift : Shift Project.ClobLimit.Frozen.«module»
    Project.ClobMarket.Frozen.«module» id id MatchDomain := by
  refine
    { sourceImports := rfl
      targetImports := rfl
      memory := rfl
      functions := ?_ }
  intro functionId hDomain
  rcases hDomain with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨Project.ClobLimit.Frozen.func8Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobLimit.Frozen.func10Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobLimit.Frozen.func11Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [MatchDomain]
  · refine ⟨Project.ClobLimit.Frozen.func13Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [MatchDomain]
  · refine ⟨Project.ClobLimit.Frozen.func14Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [MatchDomain]
  · exact ⟨Project.ClobLimit.Frozen.func17Def, rfl, rfl, func17_portable⟩
  · exact ⟨Project.ClobLimit.Frozen.func18Def, rfl, rfl, func18_portable⟩

end Project.ClobMarket.Frozen.MatchRegion
