import LeanExe.TypeSafety

/-!
Strict source equality: operand evaluation, homogeneous types, independent EqTy
admission, and exact raw-value comparison. Recursive source types remain excluded.
-/
namespace LeanExe.TypeSafety.StructuralEqualityTests

def run (program : Program) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match step program state with
      | none => state
      | some next => run program fuel next

def largest : Nat := nat64Limit - 1
def overflowAdd : Expr := .add (.nat largest) (.nat 1)
def overflowMul : Expr := .natBin .mul (.nat largest) (.nat 2)
def choiceDecls : DataDecls := [[[], [.nat64], [.bool, .word .w8]]]
def recursiveDecls : DataDecls := [[[], [.nat64, .data 0]]]

example : run [] 20 (initial (.structEq .unit .unit)) = .ret (.bool true) [] := by rfl
example : run [] 20 (initial (.structEq (.bool true) (.bool false))) = .ret (.bool false) [] := by rfl
example : run [] 20 (initial (.structEq (.nat largest) (.nat largest))) = .ret (.bool true) [] := by rfl
example : run [] 20 (initial (.structEq (.word .w8 255) (.word .w8 254))) = .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.structEq (.pair (.nat 1) (.nat 2))
    (.pair (.nat 2) (.nat 1)))) = .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.structEq (.inl .nat64 .unit) (.inr .unit (.nat 0)))) =
    .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.structEq (.arrayEmpty .nat64) (.arrayEmpty .nat64))) =
    .ret (.bool true) [] := by rfl
example : run [] 40 (initial (.structEq (.arrayPush? (.arrayEmpty .nat64) (.nat 5))
    (.arrayPush? (.arrayEmpty .nat64) (.nat 5)))) = .ret (.bool true) [] := by rfl
example : run [] 40 (initial (.structEq (.dataCtor 0 2 [.bool true, .word .w8 7])
    (.dataCtor 0 2 [.bool true, .word .w8 8]))) = .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.structEq (.dataCtor 0 0 []) (.dataCtor 0 1 [.nat 0]))) =
    .ret (.bool false) [] := by rfl

-- A differing early field cannot skip evaluation of later fields or the right operand.
example : run [] 30 (initial (.structEq (.nat 0) overflowAdd)) = .overflow .add largest 1 := by rfl
example : run [] 30 (initial (.structEq overflowMul overflowAdd)) = .overflow .mul largest 2 := by rfl
example : run [] 40 (initial (.structEq (.pair (.bool false) (.nat 0))
    (.pair (.bool true) overflowAdd))) = .overflow .add largest 1 := by rfl
example : run [] 40 (initial (.letE (.nat 4)
    (.structEq (.var 0) (.letE (.nat 3) (.var 1))))) = .ret (.bool true) [] := by rfl

-- Homogeneity and all-component equality admission are static requirements.
example : infer [] [] [] (.structEq (.nat 0) (.word .w64 0)) = none := by rfl
example : infer [] [] [] (.structEq (.word .w8 0) (.word .w32 0)) = none := by rfl
example : infer [] [] [] (.structEq (.arrayEmpty .bool) (.arrayEmpty .nat64)) = none := by rfl
example : infer [[[]], [[]]] [] [] (.structEq (.dataCtor 0 0 []) (.dataCtor 1 0 [])) = none := by rfl
example : infer choiceDecls [] [] (.structEq (.dataCtor 0 0 []) (.dataCtor 0 1 [.nat 0])) =
    some .bool := by rfl
example : infer recursiveDecls [] [] (.dataCtor 0 0 []) = some (.data 0) := by rfl
example : infer recursiveDecls [] [] (.structEq (.dataCtor 0 0 []) (.dataCtor 0 0 [])) = none := by rfl
example : infer recursiveDecls [] [] (.structEq (.arrayEmpty (.data 0))
    (.arrayEmpty (.data 0))) = none := by rfl
example : infer recursiveDecls [] [] (.structEq (.inl (.data 0) .unit)
    (.inl (.data 0) .unit)) = none := by rfl
example : infer [] [] [] (.structEq (.word .w8 256) (.word .w8 256)) = none := by rfl
example : infer [[[.data 99]]] [] [] (.structEq .unit .unit) = none := by rfl

-- Raw transitions compare raw values; returning does not establish source admission.
example : run [] 20 (initial (.structEq (.nat 0) (.word .w64 0))) = .ret (.bool false) [] := by rfl
example : run [] 20 (initial (.structEq (.word .w8 256) (.word .w8 256))) = .ret (.bool true) [] := by rfl

example : uses 0 (.structEq (.var 1) (.var 0)) = true := by rfl
example : uses 1 (.structEq (.var 1) (.var 0)) = true := by rfl
example : uses 2 (.structEq (.var 1) (.var 0)) = false := by rfl
example : admissible (.structEq .unit (.letE .unit .unit)) = false := by rfl
example : admissible (.structEq (.fst (.pair .unit .unit)) .unit) = false := by rfl

def signatures : Signatures := [⟨[.prod .nat64 .bool, .prod .nat64 .bool], .bool⟩]
def program : Program := [.structEq (.var 0) (.var 1)]
example : profileProgramWellTyped [] program signatures = true := by rfl
example : run program 40 (initial (.call 0 [.pair (.nat 2) (.bool true),
    .pair (.nat 2) (.bool true)])) = .ret (.bool true) [] := by rfl
example (execution : Steps program (initial (.call 0 [.pair (.nat 2) (.bool true),
    .pair (.nat 2) (.bool false)])) final) :
    StateTyped [] signatures final .bool ∧ ¬ Stuck program final :=
  profile_checked_type_safety rfl rfl execution

end LeanExe.TypeSafety.StructuralEqualityTests
