import LeanExe.TypeSafety

/-!
Natural zero/successor elimination: predecessor binding, outer-variable shifts,
branch checking, and strict scrutinee evaluation. Recursive examples use the
ordinary call rules and make no universal termination claim.
-/

namespace LeanExe.TypeSafety.NatCaseTests

def run (program : Program) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match step program state with
      | none => state
      | some next => run program fuel next

def largest : Nat := nat64Limit - 1
def failure : Expr := .add (.nat largest) (.nat 1)

-- Zero introduces no binding; successor introduces exactly its predecessor.
example : run [] 20 (initial (.natCase (.nat 0) (.nat 7) (.var 0))) =
    .ret (.nat 7) [] := by rfl
example : run [] 20 (initial (.natCase (.nat 1) (.nat 7) (.var 0))) =
    .ret (.nat 0) [] := by rfl
example : run [] 20 (initial (.natCase (.nat 9) (.nat 7) (.var 0))) =
    .ret (.nat 8) [] := by rfl
example : run [] 20 (initial (.natCase (.nat largest) (.nat 7) (.var 0))) =
    .ret (.nat 18446744073709551614) [] := by rfl
example : run [] 30 (initial (.letE (.nat 10)
    (.natCase (.nat 0) (.var 0) (.add (.var 0) (.var 1))))) =
    .ret (.nat 10) [] := by rfl
example : run [] 30 (initial (.letE (.nat 10)
    (.natCase (.nat 3) (.var 0) (.add (.var 0) (.var 1))))) =
    .ret (.nat 12) [] := by rfl
example : run [] 40 (initial (.letE (.nat 10)
    (.natCase (.letE (.nat 3) (.var 0)) (.var 0) (.add (.var 0) (.var 1))))) =
    .ret (.nat 12) [] := by rfl

-- Nested successor patterns shift previous predecessors and captured locals.
example : run [] 50 (initial (.letE (.nat 10)
    (.natCase (.nat 3) (.var 0)
      (.natCase (.var 0) (.var 1) (.add (.var 0) (.add (.var 1) (.var 2))))))) =
    .ret (.nat 13) [] := by rfl

-- Scrutinee errors happen first; unselected branches are never evaluated.
example : run [] 20 (initial (.natCase failure (.nat 7) (.var 0))) =
    .overflow .add largest 1 := by rfl
example : run [] 20 (initial (.natCase (.nat 0) (.nat 7) (.add (.var 0) (.nat largest)))) =
    .ret (.nat 7) [] := by rfl
example : run [] 20 (initial (.natCase (.nat 1) failure (.var 0))) =
    .ret (.nat 0) [] := by rfl
example : run [] 30 (initial (.natCase (.nat 2) (.nat 7)
    (.natBin .mul (.nat largest) (.add (.var 0) (.nat 1))))) =
    .overflow .mul largest 2 := by rfl

-- Both branches must type check, regardless of which will execute.
example : infer [] [] [] (.natCase (.nat 0) (.nat 7) (.var 0)) = some .nat64 := by rfl
example : infer [] [] [] (.natCase (.nat 0) (.bool false)
    (.natCmp .eq (.var 0) (.nat 0))) = some .bool := by rfl
example : infer [] [] [] (.natCase (.nat 0) (.bool false) (.var 0)) = none := by rfl
example : infer [] [] [] (.natCase (.nat 0) (.nat 7) (.nat nat64Limit)) = none := by rfl
example : infer [] [] [] (.natCase (.nat 1) (.nat nat64Limit) (.var 0)) = none := by rfl
example : infer [] [] [] (.natCase (.word .w8 0) (.nat 7) (.var 0)) = none := by rfl
example : infer [] [] [] (.natCase (.nat 0) (.var 0) (.var 0)) = none := by rfl
example : infer [] [] [] (.natCase (.nat 0) (.nat 7) (.var 1)) = none := by rfl
example : infer [] [] [.bool] (.natCase (.nat 3) (.var 0) (.var 1)) = some .bool := by rfl

-- Raw bad eliminations stay stuck, rather than becoming permitted failures.
example : Stuck [] (run [] 20 (initial (.natCase (.bool true) (.nat 7) (.var 0)))) := by
  constructor
  · rfl
  · intro impossible; cases impossible
example : Stuck [] (run [] 20 (initial (.natCase (.nat 0) (.var 0) (.var 0)))) := by
  constructor
  · rfl
  · intro impossible; cases impossible

-- The successor binder is required and must not be mistaken for an outer use.
example : uses 0 (.natCase (.nat 0) (.nat 7) (.var 0)) = false := by rfl
example : uses 0 (.natCase (.nat 0) (.var 0) (.var 1)) = true := by rfl
example : uses 1 (.natCase (.nat 0) (.nat 7) (.var 2)) = true := by rfl
example : uses 0 (.natCase (.nat 0) (.nat 7) (.natCase (.nat 1) (.var 0) (.var 1))) =
    false := by rfl
example : admissible (.natCase (.nat 0) (.nat 7) (.var 0)) = true := by rfl
example : admissible (.natCase (.nat 0) (.nat 7) (.nat 0)) = false := by rfl
example : admissible (.natCase (.nat 0) (.letE (.nat 1) (.nat 2)) (.var 0)) = false := by rfl
example : profileExpressionWellTyped [] [] [] (.natCase (.nat 1) (.nat 7) (.var 0))
    .nat64 = true := by rfl
example : profileProgramWellTyped [] [.natCase (.nat 0) (.nat 7) (.var 0)]
    [⟨[.nat64], .nat64⟩] = false := by rfl

-- Recursive calls use the predecessor binding without a special recursion oracle.
def countdownSignatures : Signatures := [⟨[.nat64], .nat64⟩]
def countdownProgram : Program := [.natCase (.var 0) (.nat 0) (.call 0 [.var 0])]
example : profileProgramWellTyped [] countdownProgram countdownSignatures = true := by rfl
example : run countdownProgram 60 (initial (.call 0 [.nat 3])) = .ret (.nat 0) [] := by rfl
example (execution : Steps countdownProgram (initial (.call 0 [.nat 3])) final) :
    StateTyped [] countdownSignatures final .nat64 ∧ ¬ Stuck countdownProgram final :=
  profile_checked_type_safety rfl rfl execution

end LeanExe.TypeSafety.NatCaseTests
