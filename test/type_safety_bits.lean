import LeanExe.TypeSafety

/-!
Bitwise and masked-shift regressions. These distinguish width normalization,
logical right shift, exact bit operations, and explicit count typing. Universal
mask/cancellation/periodicity laws are separately included in the theorem audit.
-/

namespace LeanExe.TypeSafety.BitTests

-- Closed 64-bit traces unfold structural bit recursion inside machine steps.
-- Raise only the elaborator's reduction depth; proofs remain kernel-checked.
set_option maxRecDepth 4096

def run (program : Program) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match step program state with
      | none => state
      | some next => run program fuel next

def largest : Nat := nat64Limit - 1
def addFailure : Expr := .add (.nat largest) (.nat 1)
def mulFailure : Expr := .natBin .mul (.nat largest) (.nat 2)

-- Exact bit patterns, high bits, and width-limited complement.
example : run [] 20 (initial (.wordBin .w8 .bitAnd (.word .w8 170) (.word .w8 204))) =
    .ret (.word .w8 136) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .bitOr (.word .w8 170) (.word .w8 204))) =
    .ret (.word .w8 238) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .bitXor (.word .w8 170) (.word .w8 204))) =
    .ret (.word .w8 102) [] := by rfl
example : run [] 20 (initial (.wordBin .w64 .bitAnd (.word .w64 largest)
    (.word .w64 9223372036854775808))) = .ret (.word .w64 9223372036854775808) [] := by rfl
example : run [] 20 (initial (.wordBin .w32 .bitXor
    (.word .w32 4294967295) (.word .w32 4294967295))) = .ret (.word .w32 0) [] := by rfl
example : run [] 20 (initial (.wordNot .w8 (.word .w8 170))) =
    .ret (.word .w8 85) [] := by rfl
example : run [] 20 (initial (.wordNot .w8 (.word .w8 0))) =
    .ret (.word .w8 255) [] := by rfl
example : run [] 20 (initial (.wordNot .w8 (.word .w8 255))) =
    .ret (.word .w8 0) [] := by rfl
example : run [] 20 (initial (.wordNot .w32 (.word .w32 0))) =
    .ret (.word .w32 4294967295) [] := by rfl
example : run [] 20 (initial (.wordNot .w64 (.word .w64 0))) =
    .ret (.word .w64 largest) [] := by rfl
example : run [] 20 (initial (.wordNot .w64 (.word .w64 9223372036854775808))) =
    .ret (.word .w64 9223372036854775807) [] := by rfl
example : run [] 30 (initial (.wordNot .w8 (.wordNot .w8 (.word .w8 170)))) =
    .ret (.word .w8 170) [] := by rfl

-- Shift counts are masked modulo the declared width, not clamped.
example : run [] 20 (initial (.wordBin .w8 .shiftLeft (.word .w8 1) (.word .w8 0))) =
    .ret (.word .w8 1) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .shiftLeft (.word .w8 1) (.word .w8 7))) =
    .ret (.word .w8 128) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .shiftLeft (.word .w8 1) (.word .w8 8))) =
    .ret (.word .w8 1) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .shiftLeft (.word .w8 1) (.word .w8 9))) =
    .ret (.word .w8 2) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .shiftLeft (.word .w8 1) (.word .w8 255))) =
    .ret (.word .w8 128) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .shiftLeft (.word .w8 255) (.word .w8 1))) =
    .ret (.word .w8 254) [] := by rfl
example : run [] 20 (initial (.wordBin .w32 .shiftLeft (.word .w32 1) (.word .w32 32))) =
    .ret (.word .w32 1) [] := by rfl
example : run [] 20 (initial (.wordBin .w32 .shiftLeft (.word .w32 1) (.word .w32 33))) =
    .ret (.word .w32 2) [] := by rfl
example : run [] 20 (initial (.wordBin .w64 .shiftLeft (.word .w64 1) (.word .w64 64))) =
    .ret (.word .w64 1) [] := by rfl
example : run [] 20 (initial (.wordBin .w64 .shiftLeft (.word .w64 1) (.word .w64 65))) =
    .ret (.word .w64 2) [] := by rfl
example : run [] 20 (initial (.wordBin .w64 .shiftLeft (.word .w64 1) (.word .w64 largest))) =
    .ret (.word .w64 9223372036854775808) [] := by rfl

-- Right shifts are unsigned division, including words with their high bit set.
example : run [] 20 (initial (.wordBin .w8 .shiftRight (.word .w8 128) (.word .w8 1))) =
    .ret (.word .w8 64) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .shiftRight (.word .w8 128) (.word .w8 7))) =
    .ret (.word .w8 1) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .shiftRight (.word .w8 128) (.word .w8 8))) =
    .ret (.word .w8 128) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .shiftRight (.word .w8 128) (.word .w8 9))) =
    .ret (.word .w8 64) [] := by rfl
example : run [] 20 (initial (.wordBin .w64 .shiftRight
    (.word .w64 largest) (.word .w64 63))) = .ret (.word .w64 1) [] := by rfl
example : run [] 20 (initial (.wordBin .w64 .shiftRight
    (.word .w64 largest) (.word .w64 64))) = .ret (.word .w64 largest) [] := by rfl

-- Shift operands, including the count, have the same explicit word width.
example : infer [] [] [] (.wordBin .w8 .shiftLeft (.word .w8 1) (.word .w8 8)) =
    some (.word .w8) := by rfl
example : infer [] [] [] (.wordBin .w8 .shiftLeft (.word .w8 1) (.nat 8)) = none := by rfl
example : infer [] [] [] (.wordBin .w8 .shiftRight (.word .w8 1) (.word .w64 8)) = none := by rfl
example : infer [] [] [] (.wordBin .w8 .bitXor (.word .w8 1) (.word .w32 1)) = none := by rfl
example : infer [] [] [] (.wordNot .w8 (.word .w8 255)) = some (.word .w8) := by rfl
example : infer [] [] [] (.wordNot .w8 (.word .w32 255)) = none := by rfl
example : infer [] [] [] (.wordNot .w8 (.nat 255)) = none := by rfl
example : Stuck [] (run [] 20 (initial
    (.wordBin .w8 .shiftLeft (.word .w8 1) (.word .w32 8)))) := by
  constructor
  · rfl
  · intro impossible; cases impossible

-- No bitwise operand is skipped because another looks decisive.
example : run [] 40 (initial (.wordBin .w8 .bitAnd (.word .w8 0)
    (.wordOfNat .w8 addFailure))) = .overflow .add largest 1 := by rfl
example : run [] 40 (initial (.wordBin .w8 .shiftLeft (.word .w8 0)
    (.wordOfNat .w8 mulFailure))) = .overflow .mul largest 2 := by rfl
example : run [] 40 (initial (.wordBin .w8 .shiftRight
    (.wordOfNat .w8 addFailure) (.wordOfNat .w8 mulFailure))) =
    .overflow .add largest 1 := by rfl
example : run [] 30 (initial (.wordNot .w8 (.wordOfNat .w8 mulFailure))) =
    .overflow .mul largest 2 := by rfl
example : run [] 40 (initial (.letE (.word .w8 1)
    (.wordBin .w8 .shiftLeft (.letE (.word .w8 3) (.var 0)) (.var 0)))) =
    .ret (.word .w8 6) [] := by rfl

-- Derived complement preserves the occurrence restriction.
example : uses 0 (.wordNot .w8 (.var 0)) = true := by rfl
example : uses 1 (.wordNot .w8 (.var 0)) = false := by rfl
example : admissible (.wordNot .w8 (.fst (.var 0))) = false := by rfl
example : profileExpressionWellTyped [] [] []
    (.letE (.word .w8 170) (.wordNot .w8 (.var 0))) (.word .w8) = true := by rfl

-- Composition across a checked function boundary: one-bit rotation of 0x81.
def rotateSignatures : Signatures := [⟨[.word .w8], .word .w8⟩]
def rotateProgram : Program := [.wordBin .w8 .bitOr
  (.wordBin .w8 .shiftLeft (.var 0) (.word .w8 1))
  (.wordBin .w8 .shiftRight (.var 0) (.word .w8 7))]
example : profileProgramWellTyped [] rotateProgram rotateSignatures = true := by rfl
example : run rotateProgram 50 (initial (.call 0 [.word .w8 129])) =
    .ret (.word .w8 3) [] := by rfl
example (execution : Steps rotateProgram (initial (.call 0 [.word .w8 129])) final) :
    StateTyped [] rotateSignatures final (.word .w8) ∧ ¬ Stuck rotateProgram final :=
  profile_checked_type_safety rfl rfl execution

end LeanExe.TypeSafety.BitTests
