import Project.FunctionRegion.Exec
import Project.ClobFindBest.Program
import Project.ClobMatchFuel.Program

namespace Project.ClobMatchFuel.SearchRegion
open Project.FunctionRegion

def SearchDomain (id : Nat) : Prop :=
  id = 1 ∨ id = 4 ∨ id = 5 ∨ id = 7 ∨ id = 12

def searchRename : Nat → Nat
  | 1 => 2
  | 4 => 5
  | 5 => 6
  | 7 => 8
  | 12 => 18
  | id => id

def searchTypeRename : Nat → Nat := searchRename

theorem searchShift : Shift Project.ClobFindBest.module
    Project.ClobMatchFuel.module searchRename searchTypeRename SearchDomain := by
  refine { sourceImports := rfl, targetImports := rfl, memory := rfl, functions := ?_ }
  intro id hDomain
  rcases hDomain with rfl | rfl | rfl | rfl | rfl
  · refine ⟨Project.ClobFindBest.func1Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobFindBest.func4Def, rfl, rfl, ?_⟩
    prove_portable
  · refine ⟨Project.ClobFindBest.func5Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [SearchDomain]
  · refine ⟨Project.ClobFindBest.func7Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [SearchDomain]
  · refine ⟨Project.ClobFindBest.func12Def, rfl, rfl, ?_⟩
    prove_portable
    all_goals simp [SearchDomain]

end Project.ClobMatchFuel.SearchRegion
