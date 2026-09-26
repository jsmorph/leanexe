import Project.FunctionRegion.Exec
import Project.ClobMatchFuel.FrozenProgram
import Project.ClobLimit.FrozenProgram

/-!
# Reused search-function region

The matching and limit artifacts contain the same six search functions at
different indices.  This module records their exact function renaming and
their closed portable syntax.
-/

namespace Project.ClobLimit.Frozen.SearchRegion

open Project.FunctionRegion

def SearchDomain (id : Nat) : Prop :=
  id = 2 ∨ id = 5 ∨ id = 6 ∨ id = 7 ∨ id = 8 ∨ id = 9

def searchRename : Nat → Nat
  | 2 => 8
  | 5 => 10
  | 6 => 11
  | 7 => 12
  | 8 => 13
  | 9 => 14
  | id => id

/-- The reused functions' nominal types occupy the corresponding embedded
positions in the target module's distinct type-index space. -/
def searchTypeRename : Nat → Nat := searchRename

theorem searchShift : Shift Project.ClobMatchFuel.Frozen.«module»
    Project.ClobLimit.Frozen.«module» searchRename searchTypeRename SearchDomain := by
  refine
    { sourceImports := rfl
      targetImports := rfl
      memory := rfl
      functions := ?_ }
  intro id hDomain
  rcases hDomain with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨Project.ClobMatchFuel.Frozen.func2Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobMatchFuel.Frozen.func5Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobMatchFuel.Frozen.func6Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [SearchDomain]
  · refine ⟨Project.ClobMatchFuel.Frozen.func7Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobMatchFuel.Frozen.func8Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [SearchDomain]
  · refine ⟨Project.ClobMatchFuel.Frozen.func9Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [SearchDomain]

end Project.ClobLimit.Frozen.SearchRegion
