import Project.FunctionRegion.Exec
import Project.ClobFindBest.FrozenProgram
import Project.ClobMatchFuel.FrozenProgram

namespace Project.ClobMatchFuel.Frozen.SearchRegion
open Project.FunctionRegion

def SearchDomain (id : Nat) : Prop :=
  id = 1 ∨ id = 4 ∨ id = 5 ∨ id = 7

def searchRename : Nat → Nat
  | 1 => 2
  | 4 => 5
  | 5 => 6
  | 7 => 8
  | id => id

def searchTypeRename : Nat → Nat := searchRename

theorem searchShift : Shift Project.ClobFindBest.Frozen.module
    Project.ClobMatchFuel.Frozen.module searchRename searchTypeRename SearchDomain := by
  refine { sourceImports := rfl, targetImports := rfl, memory := rfl, functions := ?_ }
  intro id hDomain
  rcases hDomain with rfl | rfl | rfl | rfl
  · refine ⟨Project.ClobFindBest.Frozen.func1Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobFindBest.Frozen.func4Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobFindBest.Frozen.func5Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [SearchDomain]
  · refine ⟨Project.ClobFindBest.Frozen.func7Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [SearchDomain]

end Project.ClobMatchFuel.Frozen.SearchRegion
