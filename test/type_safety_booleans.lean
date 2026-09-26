import LeanExe.TypeSafety

/-!
Strict derived Boolean operations. Truth tables, source admission, captured
scopes, and failure order distinguish these helpers from conditional evaluation.
-/

namespace LeanExe.TypeSafety.BooleanTests

def run (program : Program) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match step program state with
      | none => state
      | some next => run program fuel next

def largest : Nat := nat64Limit - 1
def failureA : Expr := .natCmp .eq (.add (.nat largest) (.nat 1)) (.nat 0)
def failureB : Expr := .natCmp .eq (.natBin .mul (.nat largest) (.nat 2)) (.nat 0)

-- Truth tables are checked through actual machine execution.
example : run [] 20 (initial (.boolNot (.bool false))) = .ret (.bool true) [] := by rfl
example : run [] 20 (initial (.boolNot (.bool true))) = .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.boolAnd (.bool false) (.bool false))) = .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.boolAnd (.bool false) (.bool true))) = .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.boolAnd (.bool true) (.bool false))) = .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.boolAnd (.bool true) (.bool true))) = .ret (.bool true) [] := by rfl
example : run [] 30 (initial (.boolOr (.bool false) (.bool false))) = .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.boolOr (.bool false) (.bool true))) = .ret (.bool true) [] := by rfl
example : run [] 30 (initial (.boolOr (.bool true) (.bool false))) = .ret (.bool true) [] := by rfl
example : run [] 30 (initial (.boolOr (.bool true) (.bool true))) = .ret (.bool true) [] := by rfl
example : run [] 30 (initial (.boolXor (.bool false) (.bool false))) = .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.boolXor (.bool false) (.bool true))) = .ret (.bool true) [] := by rfl
example : run [] 30 (initial (.boolXor (.bool true) (.bool false))) = .ret (.bool true) [] := by rfl
example : run [] 30 (initial (.boolXor (.bool true) (.bool true))) = .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.boolEq (.bool false) (.bool false))) = .ret (.bool true) [] := by rfl
example : run [] 30 (initial (.boolEq (.bool false) (.bool true))) = .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.boolEq (.bool true) (.bool false))) = .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.boolEq (.bool true) (.bool true))) = .ret (.bool true) [] := by rfl

-- Both operands are evaluated even when the first determines the Boolean result.
example : run [] 40 (initial (.boolAnd (.bool false) failureA)) =
    .overflow .add largest 1 := by rfl
example : run [] 40 (initial (.boolOr (.bool true) failureA)) =
    .overflow .add largest 1 := by rfl
example : run [] 40 (initial (.boolXor failureA failureB)) =
    .overflow .add largest 1 := by rfl
example : run [] 40 (initial (.boolEq failureB failureA)) =
    .overflow .mul largest 2 := by rfl
example : run [] 30 (initial (.boolNot failureA)) = .overflow .add largest 1 := by rfl
example : run [] 20 (initial (.ifE (.bool false) failureA (.bool false))) =
    .ret (.bool false) [] := by rfl
example : run [] 20 (initial (.ifE (.bool true) (.bool true) failureA)) =
    .ret (.bool true) [] := by rfl

-- Open operands remain in the caller's context; generated bodies capture neither.
example : run [] 50 (initial (.letE (.bool true)
    (.boolXor (.letE (.bool false) (.var 0)) (.var 0)))) =
    .ret (.bool true) [] := by rfl
example : run [] 50 (initial (.letE (.bool false)
    (.boolEq (.var 0) (.letE (.bool true) (.var 0))))) =
    .ret (.bool false) [] := by rfl
example : run [] 40 (.eval (.boolAnd (.var 0) (.var 1)) [.bool true, .bool false] []) =
    .ret (.bool false) [] := by rfl

-- Both operands must be Boolean even if an ill-typed raw expression happens to return.
example : infer [] [] [] (.boolNot (.nat 0)) = none := by rfl
example : infer [] [] [] (.boolAnd (.bool false) (.nat 0)) = none := by rfl
example : infer [] [] [] (.boolOr (.bool true) .unit) = none := by rfl
example : infer [] [] [] (.boolXor (.word .w8 1) (.bool true)) = none := by rfl
example : infer [] [] [] (.boolEq (.nat 0) (.nat 0)) = none := by rfl
example : run [] 30 (initial (.boolAnd (.bool false) (.nat 0))) =
    .ret (.bool false) [] := by rfl
example : infer [] [] [] (.boolEq (.bool false) (.bool true)) = some .bool := by rfl
example : infer [] [] [.bool, .bool] (.boolOr (.var 0) (.var 1)) = some .bool := by rfl

-- Relevance checks the original operands and both generated product fields.
example : uses 0 (.boolAnd (.var 1) (.var 0)) = true := by rfl
example : uses 1 (.boolAnd (.var 1) (.var 0)) = true := by rfl
example : uses 2 (.boolAnd (.var 1) (.var 0)) = false := by rfl
example : uses 0 (.boolNot (.var 1)) = false := by rfl
example : admissible (.boolAnd (.bool true) (.letE (.bool true) (.bool false))) = false := by rfl
example : admissible (.boolNot (.fst (.pair (.bool true) (.bool false)))) = false := by rfl
example : profileExpressionWellTyped [] [] []
    (.letE (.bool true) (.boolNot (.var 0))) .bool = true := by rfl
example : profileExpressionWellTyped [] [] []
    (.letE (.bool true) (.boolAnd (.var 0) (.var 0))) .bool = true := by rfl

def equalSignatures : Signatures := [⟨[.bool, .bool], .bool⟩]
def equalProgram : Program := [.boolEq (.var 0) (.var 1)]
example : profileProgramWellTyped [] equalProgram equalSignatures = true := by rfl
example : run equalProgram 40 (initial (.call 0 [.bool false, .bool true])) =
    .ret (.bool false) [] := by rfl
example (execution : Steps equalProgram (initial (.call 0 [.bool false, .bool true])) final) :
    StateTyped [] equalSignatures final .bool ∧ ¬ Stuck equalProgram final :=
  profile_checked_type_safety rfl rfl execution

end LeanExe.TypeSafety.BooleanTests
