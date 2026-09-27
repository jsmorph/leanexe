import LeanExe.TypeSafety

/-!
Bounded-natural regression examples. The fuel-limited runner checks specified
behavior, not termination. Universal primitive and machine laws are audited
separately by the maintained gate.
-/

namespace LeanExe.TypeSafety.NaturalTests

def run (program : Program) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match step program state with
      | none => state
      | some next => run program fuel next

def largest : Nat := nat64Limit - 1
def addFailure : Expr := .add (.nat largest) (.nat 1)
def mulFailure : Expr := .natBin .mul (.nat largest) (.nat 2)

-- Raw primitive computation does not silently sanitize malformed operands.
example : evalNatBin .sub nat64Limit 0 = .value nat64Limit := by rfl
example : infer [] [] [] (.natBin .sub (.nat nat64Limit) (.nat 0)) = none := by rfl
example : evalNatBin .add largest 1 = .overflow .add := by rfl
example : evalNatBin .mul largest 2 = .overflow .mul := by rfl
example : evalNatBin .sub 1 largest = .value 0 := by rfl
example : evalNatBin .min largest largest = .value largest := by rfl

-- Exact source types, operand validation, and derived forms.
example : infer [] [] [] (.natBin .sub (.nat 3) (.nat 7)) = some .nat64 := by rfl
example : infer [] [] [] mulFailure = some .nat64 := by rfl
example : infer [] [] [] (.natBin .div (.nat 3) (.nat 0)) = some .nat64 := by rfl
example : infer [] [] [] (.natBin .mod (.nat 3) (.nat 0)) = some .nat64 := by rfl
example : infer [] [] [] (.natBin .min (.nat 3) (.nat 7)) = some .nat64 := by rfl
example : infer [] [] [] (.natBin .max (.nat 3) (.nat 7)) = some .nat64 := by rfl
example : infer [] [] [] (.natCmp .eq (.nat 3) (.nat 7)) = some .bool := by rfl
example : infer [] [] [] (.natCmp .lt (.nat 3) (.nat 7)) = some .bool := by rfl
example : infer [] [] [] (.natCmp .le (.nat 3) (.nat 7)) = some .bool := by rfl
example : infer [] [] [] (.natBin .mul (.bool false) (.nat 7)) = none := by rfl
example : infer [] [] [] (.natBin .div (.nat 7) .unit) = none := by rfl
example : infer [] [] [] (.natCmp .eq (.bool false) (.bool false)) = none := by rfl
example : infer [] [] [] (.natCmp .lt (.nat nat64Limit) (.nat 0)) = none := by rfl
example : infer [] [] [] (.succ (.nat 9)) = some .nat64 := by rfl
example : infer [] [] [] (.pred (.nat 0)) = some .nat64 := by rfl
example : infer [] [] [] (.boolToNat (.bool true)) = some .nat64 := by rfl
example : infer [] [] [] (.boolToNat (.nat 1)) = none := by rfl

-- Arithmetic boundary behavior is deliberately not uniform wrapping.
example : run [] 20 (initial (.natBin .mul (.nat largest) (.nat 1))) =
    .ret (.nat largest) [] := by rfl
example : run [] 20 (initial (.natBin .mul (.nat largest) (.nat 0))) =
    .ret (.nat 0) [] := by rfl
example : run [] 20 (initial (.natBin .mul (.nat 4294967296) (.nat 4294967295))) =
    .ret (.nat 18446744069414584320) [] := by rfl
example : run [] 20 (initial (.natBin .mul (.nat 4294967296) (.nat 4294967296))) =
    .overflow .mul 4294967296 4294967296 := by rfl
example : run [] 20 (initial mulFailure) = .overflow .mul largest 2 := by rfl
example : run [] 20 (initial (.natBin .sub (.nat 3) (.nat 7))) =
    .ret (.nat 0) [] := by rfl
example : run [] 20 (initial (.natBin .sub (.nat 7) (.nat 3))) =
    .ret (.nat 4) [] := by rfl
example : run [] 20 (initial (.natBin .sub (.nat largest) (.nat largest))) =
    .ret (.nat 0) [] := by rfl
example : run [] 20 (initial (.natBin .div (.nat largest) (.nat 0))) =
    .ret (.nat 0) [] := by rfl
example : run [] 20 (initial (.natBin .mod (.nat largest) (.nat 0))) =
    .ret (.nat largest) [] := by rfl
example : run [] 20 (initial (.natBin .div (.nat 7) (.nat 3))) =
    .ret (.nat 2) [] := by rfl
example : run [] 20 (initial (.natBin .mod (.nat 7) (.nat 3))) =
    .ret (.nat 1) [] := by rfl
example : run [] 20 (initial (.natBin .div (.nat 0) (.nat 0))) =
    .ret (.nat 0) [] := by rfl
example : run [] 20 (initial (.natBin .mod (.nat 0) (.nat 0))) =
    .ret (.nat 0) [] := by rfl
example : run [] 20 (initial (.natBin .min (.nat largest) (.nat 0))) =
    .ret (.nat 0) [] := by rfl
example : run [] 20 (initial (.natBin .max (.nat 0) (.nat largest))) =
    .ret (.nat largest) [] := by rfl
example : run [] 20 (initial (.succ (.nat largest))) = .overflow .add largest 1 := by rfl
example : run [] 20 (initial (.pred (.nat 0))) = .ret (.nat 0) [] := by rfl
example : run [] 20 (initial (.boolToNat (.bool true))) = .ret (.nat 1) [] := by rfl
example : run [] 20 (initial (.boolToNat (.bool false))) = .ret (.nat 0) [] := by rfl

-- Comparison boundaries and branch use.
example : run [] 20 (initial (.natCmp .eq (.nat largest) (.nat largest))) =
    .ret (.bool true) [] := by rfl
example : run [] 20 (initial (.natCmp .eq (.nat 0) (.nat largest))) =
    .ret (.bool false) [] := by rfl
example : run [] 20 (initial (.natCmp .lt (.nat largest) (.nat largest))) =
    .ret (.bool false) [] := by rfl
example : run [] 20 (initial (.natCmp .lt (.nat 0) (.nat largest))) =
    .ret (.bool true) [] := by rfl
example : run [] 20 (initial (.natCmp .le (.nat largest) (.nat largest))) =
    .ret (.bool true) [] := by rfl
example : run [] 20 (initial (.natCmp .le (.nat largest) (.nat 0))) =
    .ret (.bool false) [] := by rfl
example : run [] 30 (initial (.ifE (.natCmp .lt (.nat 1) (.nat 2))
    (.nat 9) mulFailure)) = .ret (.nat 9) [] := by rfl

-- All operands are evaluated, including apparently decisive zero/min inputs.
example : run [] 30 (initial (.natBin .mul (.nat 0) mulFailure)) =
    .overflow .mul largest 2 := by rfl
example : run [] 30 (initial (.natBin .min (.nat 0) mulFailure)) =
    .overflow .mul largest 2 := by rfl
example : run [] 30 (initial (.natBin .div mulFailure (.nat 0))) =
    .overflow .mul largest 2 := by rfl
example : run [] 30 (initial (.natBin .max addFailure mulFailure)) =
    .overflow .add largest 1 := by rfl
example : run [] 30 (initial (.natCmp .eq mulFailure addFailure)) =
    .overflow .mul largest 2 := by rfl
example : run [] 30 (initial (.boolToNat (.natCmp .le addFailure (.nat 0)))) =
    .overflow .add largest 1 := by rfl

-- A left operand's local binding cannot overwrite the right operand's context.
example : run [] 40 (initial (.letE (.nat 7)
    (.natBin .sub (.letE (.nat 10) (.var 0)) (.var 0)))) =
    .ret (.nat 3) [] := by rfl
example : run [] 40 (initial (.letE (.nat 7)
    (.natCmp .lt (.letE (.nat 10) (.var 0)) (.var 0)))) =
    .ret (.bool false) [] := by rfl

-- Relevance reaches both operands and all derived-form arguments.
example : uses 0 (.natBin .mul (.nat 2) (.var 0)) = true := by rfl
example : uses 0 (.natCmp .eq (.var 0) (.nat 0)) = true := by rfl
example : admissible (.natBin .div (.nat 7) (.letE (.nat 1) (.nat 2))) = false := by rfl
example : admissible (.natCmp .lt (.fst (.var 0)) (.nat 2)) = false := by rfl
example : profileExpressionWellTyped [] [] []
    (.letE (.nat 7) (.natBin .mul (.var 0) (.var 0))) .nat64 = true := by rfl
example : profileExpressionWellTyped [] [] []
    (.letE (.nat 7) (.natCmp .le (.var 0) (.var 0))) .bool = true := by rfl

-- Ill-shaped frames and forged failures cannot be classified as successful progress.
example : Stuck [] (.ret (.bool true) [.natBinRight .mul (.nat 1)]) := by
  simp [Stuck, step, Terminal]
example : Stuck [] (.ret (.nat 1) [.natCmpRight .eq .unit]) := by
  simp [Stuck, step, Terminal]
example : ¬ Terminal (.overflow .mul 1 1) := by
  unfold Terminal Overflow
  decide
example : ¬ Terminal (.overflow .add largest 0) := by
  unfold Terminal Overflow
  decide
example : ¬ Terminal (.overflow .mul nat64Limit 2) := by
  unfold Terminal Overflow
  decide
example : Terminal (.overflow .mul largest 2) := by
  unfold Terminal Overflow
  decide

-- Recursive countdown uses the new arithmetic without a termination premise.
def countdownSignatures : Signatures := [⟨[.nat64], .nat64⟩]
def countdownProgram : Program := [
  .ifE (.natCmp .eq (.var 0) (.nat 0)) (.nat 0)
    (.call 0 [.pred (.var 0)])]
example : profileProgramWellTyped [] countdownProgram countdownSignatures = true := by rfl
example : run countdownProgram 100 (initial (.call 0 [.nat 3])) =
    .ret (.nat 0) [] := by rfl
example (execution : Steps countdownProgram (initial (.call 0 [.nat 3])) final) :
    StateTyped [] countdownSignatures final .nat64 ∧ ¬ Stuck countdownProgram final :=
  profile_checked_type_safety rfl rfl execution

end LeanExe.TypeSafety.NaturalTests
