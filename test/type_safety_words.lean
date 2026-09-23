import LeanExe.TypeSafety

/-!
Word arithmetic and conversion regressions. Expected values distinguish modular
words from bounded naturals, width mismatches from conversions, and narrowing
from value-preserving widening. Fuel is only a regression-test runner.
-/

namespace LeanExe.TypeSafety.WordTests

def run (program : Program) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match step program state with
      | none => state
      | some next => run program fuel next

def largest : Nat := nat64Limit - 1
def naturalFailure : Expr := .add (.nat largest) (.nat 1)
def otherFailure : Expr := .natBin .mul (.nat largest) (.nat 2)

-- Canonical literals and signatures retain their exact width.
example : infer [] [] [] (.word .w8 255) = some (.word .w8) := by rfl
example : infer [] [] [] (.word .w8 256) = none := by rfl
example : infer [] [] [] (.word .w32 4294967295) = some (.word .w32) := by rfl
example : infer [] [] [] (.word .w32 4294967296) = none := by rfl
example : infer [] [] [] (.word .w64 largest) = some (.word .w64) := by rfl
example : infer [] [] [] (.word .w64 nat64Limit) = none := by rfl
example : infer [] [] [] (.wordBin .w8 .add (.word .w8 255) (.word .w8 1)) =
    some (.word .w8) := by rfl
example : infer [] [] [] (.wordBin .w8 .add (.word .w8 1) (.word .w32 1)) = none := by rfl
example : infer [] [] [] (.wordBin .w8 .add (.nat 1) (.word .w8 1)) = none := by rfl
example : infer [] [] [] (.wordCmp .w8 .eq (.word .w8 1) (.word .w8 2)) =
    some .bool := by rfl
example : infer [] [] [] (.wordCmp .w8 .eq (.word .w8 1) (.word .w32 1)) = none := by rfl
example : infer [] [] [] (.wordOfNat .w8 (.nat 256)) = some (.word .w8) := by rfl
example : infer [] [] [] (.wordOfNat .w8 (.nat nat64Limit)) = none := by rfl
example : infer [] [] [] (.wordOfNat .w8 (.word .w64 256)) = none := by rfl
example : infer [] [] [] (.wordToNat .w8 (.word .w8 255)) = some .nat64 := by rfl
example : infer [] [] [] (.wordToNat .w8 (.word .w32 255)) = none := by rfl
example : infer [] [] [] (.wordCast .w8 .w32 (.word .w8 255)) =
    some (.word .w32) := by rfl
example : infer [] [] [] (.wordCast .w8 .w32 (.word .w32 255)) = none := by rfl

-- Addition and multiplication wrap, even at the Nat64 overflow boundary.
example : run [] 20 (initial (.wordBin .w8 .add (.word .w8 255) (.word .w8 1))) =
    .ret (.word .w8 0) [] := by rfl
example : run [] 20 (initial (.wordBin .w32 .add (.word .w32 4294967295) (.word .w32 1))) =
    .ret (.word .w32 0) [] := by rfl
example : run [] 20 (initial (.wordBin .w64 .add (.word .w64 largest) (.word .w64 1))) =
    .ret (.word .w64 0) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .mul (.word .w8 255) (.word .w8 255))) =
    .ret (.word .w8 1) [] := by rfl
example : run [] 20 (initial (.wordBin .w32 .mul (.word .w32 65536) (.word .w32 65536))) =
    .ret (.word .w32 0) [] := by rfl
example : run [] 20 (initial
    (.wordBin .w64 .mul (.word .w64 4294967296) (.word .w64 4294967296))) =
    .ret (.word .w64 0) [] := by rfl

-- Modular subtraction must not accidentally use saturating Nat subtraction.
example : run [] 20 (initial (.wordBin .w8 .sub (.word .w8 0) (.word .w8 1))) =
    .ret (.word .w8 255) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .sub (.word .w8 0) (.word .w8 255))) =
    .ret (.word .w8 1) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .sub (.word .w8 9) (.word .w8 4))) =
    .ret (.word .w8 5) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .sub (.word .w8 255) (.word .w8 255))) =
    .ret (.word .w8 0) [] := by rfl
example : run [] 20 (initial (.wordBin .w64 .sub (.word .w64 0) (.word .w64 1))) =
    .ret (.word .w64 largest) [] := by rfl

-- Division/remainder by zero are ordinary specified results, not traps.
example : run [] 20 (initial (.wordBin .w8 .div (.word .w8 255) (.word .w8 0))) =
    .ret (.word .w8 0) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .mod (.word .w8 255) (.word .w8 0))) =
    .ret (.word .w8 255) [] := by rfl
example : run [] 20 (initial (.wordBin .w64 .div (.word .w64 largest) (.word .w64 1))) =
    .ret (.word .w64 largest) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .div (.word .w8 255) (.word .w8 2))) =
    .ret (.word .w8 127) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .mod (.word .w8 255) (.word .w8 2))) =
    .ret (.word .w8 1) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .min (.word .w8 128) (.word .w8 127))) =
    .ret (.word .w8 127) [] := by rfl
example : run [] 20 (initial (.wordBin .w8 .max (.word .w8 128) (.word .w8 127))) =
    .ret (.word .w8 128) [] := by rfl

-- Comparisons are unsigned, including values with the high bit set.
example : run [] 20 (initial (.wordCmp .w8 .lt (.word .w8 128) (.word .w8 127))) =
    .ret (.bool false) [] := by rfl
example : run [] 20 (initial (.wordCmp .w64 .le (.word .w64 0) (.word .w64 largest))) =
    .ret (.bool true) [] := by rfl
example : run [] 20 (initial (.wordCmp .w8 .eq (.word .w8 255) (.word .w8 255))) =
    .ret (.bool true) [] := by rfl
example : run [] 20 (initial (.wordCmp .w8 .lt (.word .w8 255) (.word .w8 255))) =
    .ret (.bool false) [] := by rfl

-- Conversions make every change in numeric representation explicit.
example : run [] 20 (initial (.wordOfNat .w8 (.nat 256))) = .ret (.word .w8 0) [] := by rfl
example : run [] 20 (initial (.wordOfNat .w8 (.nat largest))) = .ret (.word .w8 255) [] := by rfl
example : run [] 20 (initial (.wordOfNat .w32 (.nat largest))) =
    .ret (.word .w32 4294967295) [] := by rfl
example : run [] 20 (initial (.wordOfNat .w64 (.nat largest))) =
    .ret (.word .w64 largest) [] := by rfl
example : run [] 20 (initial (.wordToNat .w64 (.word .w64 largest))) =
    .ret (.nat largest) [] := by rfl
example : run [] 20 (initial (.wordCast .w8 .w64 (.word .w8 255))) =
    .ret (.word .w64 255) [] := by rfl
example : run [] 20 (initial (.wordCast .w64 .w8 (.word .w64 256))) =
    .ret (.word .w8 0) [] := by rfl
example : run [] 20 (initial (.wordCast .w8 .w8 (.word .w8 255))) =
    .ret (.word .w8 255) [] := by rfl
example : run [] 30 (initial (.wordCast .w64 .w8 (.wordCast .w8 .w64 (.word .w8 255)))) =
    .ret (.word .w8 255) [] := by rfl
example : run [] 30 (initial (.wordCast .w8 .w64 (.wordCast .w64 .w8 (.word .w64 256)))) =
    .ret (.word .w64 0) [] := by rfl

-- Natural-expression failures occur before conversion; words do not mask them.
example : run [] 30 (initial (.wordOfNat .w8 naturalFailure)) =
    .overflow .add largest 1 := by rfl
example : run [] 40 (initial (.wordBin .w8 .min (.word .w8 0)
    (.wordOfNat .w8 otherFailure))) = .overflow .mul largest 2 := by rfl
example : run [] 40 (initial (.wordBin .w8 .add
    (.wordOfNat .w8 naturalFailure) (.wordOfNat .w8 otherFailure))) =
    .overflow .add largest 1 := by rfl
example : run [] 40 (initial (.wordCmp .w8 .eq
    (.wordOfNat .w8 otherFailure) (.wordOfNat .w8 naturalFailure))) =
    .overflow .mul largest 2 := by rfl
example : run [] 40 (initial (.letE (.word .w8 7)
    (.wordBin .w8 .sub (.letE (.word .w8 10) (.var 0)) (.var 0)))) =
    .ret (.word .w8 3) [] := by rfl

-- Relevance reaches operations and conversions without introducing binders.
example : uses 0 (.wordCast .w8 .w64 (.var 0)) = true := by rfl
example : uses 0 (.wordCmp .w8 .eq (.word .w8 0) (.var 0)) = true := by rfl
example : profileExpressionWellTyped [] [] []
    (.letE (.word .w8 255) (.wordBin .w8 .mul (.var 0) (.var 0))) (.word .w8) = true := by rfl
example : profileExpressionWellTyped [] [] []
    (.letE (.word .w8 255) (.word .w8 0)) (.word .w8) = false := by rfl
example : admissible (.wordToNat .w8 (.fst (.var 0))) = false := by rfl

-- Raw execution checks width tags; type rejection is not the only safeguard.
example : Stuck [] (run [] 20 (initial
    (.wordBin .w8 .add (.word .w32 1) (.word .w8 2)))) := by
  constructor
  · rfl
  · intro impossible; cases impossible
example : Stuck [] (run [] 20 (initial
    (.wordBin .w8 .add (.word .w8 1) (.word .w32 2)))) := by
  constructor
  · rfl
  · intro impossible; cases impossible
example : Stuck [] (run [] 20 (initial
    (.wordCmp .w8 .eq (.word .w8 1) (.word .w32 1)))) := by
  constructor
  · rfl
  · intro impossible; cases impossible
example : Stuck [] (run [] 20 (initial (.wordCast .w8 .w64 (.word .w32 255)))) := by
  constructor
  · rfl
  · intro impossible; cases impossible
example : Stuck [] (run [] 20 (initial (.wordToNat .w8 (.word .w32 255)))) := by
  constructor
  · rfl
  · intro impossible; cases impossible
example : Stuck [] (run [] 20 (initial (.wordOfNat .w8 (.word .w64 256)))) := by
  constructor
  · rfl
  · intro impossible; cases impossible

-- Words compose with heterogeneous data, homogeneous arrays, and function signatures.
example : infer [[[.word .w8, .word .w32]]] [] []
    (.dataCtor 0 0 [.word .w8 255, .word .w32 256]) = some (.data 0) := by rfl
example : infer [[[.word .w8]]] [] [] (.dataCtor 0 0 [.word .w8 256]) = none := by rfl
example : infer [] [] [] (.arrayPush? (.arrayEmpty (.word .w8)) (.word .w32 1)) = none := by rfl
example : run [] 20 (initial (.arrayPush? (.arrayEmpty (.word .w8)) (.word .w8 255))) =
    .ret (.inr (.array [.word .w8 255])) [] := by rfl
def castSignatures : Signatures := [⟨[.word .w8], .word .w64⟩]
def castProgram : Program := [.wordCast .w8 .w64 (.var 0)]
example : profileProgramWellTyped [] castProgram castSignatures = true := by rfl
example : run castProgram 30 (initial (.call 0 [.word .w8 255])) =
    .ret (.word .w64 255) [] := by rfl
example (execution : Steps castProgram (initial (.call 0 [.word .w8 255])) final) :
    StateTyped [] castSignatures final (.word .w64) ∧ ¬ Stuck castProgram final :=
  profile_checked_type_safety rfl rfl execution

end LeanExe.TypeSafety.WordTests
