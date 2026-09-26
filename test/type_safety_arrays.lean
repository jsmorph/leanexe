import LeanExe.TypeSafety

/-!
Behavior checks for the abstract persistent-array operations. The fuel-limited
runner is only a test helper. Universal length bounds and operation laws belong
to ArrayValues; the machine safety theorem quantifies over all finite executions.
-/

namespace LeanExe.TypeSafety.ArrayTests

def run (program : Program) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match step program state with
      | none => state
      | some next => run program fuel next

def largest : Nat := nat64Limit - 1
def overflowOne : Expr := .add (.nat largest) (.nat 1)
def overflowTwo : Expr := .add (.nat largest) (.nat 2)
def sample : Value := .array [.nat 11, .nat 22, .nat 33]

-- Empty construction retains an explicit item type in the expression.
example : run [] 10 (initial (.arrayEmpty .nat64)) = .ret (.array []) [] := by rfl
example : run [] 10 (initial (.arraySize (.arrayEmpty .nat64))) =
    .ret (.nat 0) [] := by rfl
example : ProfileTyped [] [] [] (.arrayEmpty .nat64) (.array .nat64) :=
  ⟨.arrayEmpty .nat64, rfl⟩

-- Boundary indices include zero, the last element, and the exclusive endpoint.
example : run [] 20 (.eval (.arraySize (.var 0)) [sample] []) =
    .ret (.nat 3) [] := by rfl
example : run [] 20 (.eval (.arrayGet? (.var 0) (.nat 0)) [sample] []) =
    .ret (.inr (.nat 11)) [] := by rfl
example : run [] 20 (.eval (.arrayGet? (.var 0) (.nat 2)) [sample] []) =
    .ret (.inr (.nat 33)) [] := by rfl
example : run [] 20 (.eval (.arrayGet? (.var 0) (.nat 3)) [sample] []) =
    .ret (.inl .unit) [] := by rfl
example : run [] 20 (.eval (.arrayGet? (.var 0) (.nat largest)) [sample] []) =
    .ret (.inl .unit) [] := by rfl
example : run [] 20 (initial (.arrayGet? (.arrayEmpty .nat64) (.nat 0))) =
    .ret (.inl .unit) [] := by rfl

-- Set returns a fresh sequence; it preserves order and all other elements.
example : run [] 30 (.eval (.arraySet? (.var 0) (.nat 1) (.nat 99)) [sample] []) =
    .ret (.inr (.array [.nat 11, .nat 99, .nat 33])) [] := by rfl
example : run [] 30 (.eval (.arraySet? (.var 0) (.nat 0) (.nat 99)) [sample] []) =
    .ret (.inr (.array [.nat 99, .nat 22, .nat 33])) [] := by rfl
example : run [] 30 (.eval (.arraySet? (.var 0) (.nat 2) (.nat 99)) [sample] []) =
    .ret (.inr (.array [.nat 11, .nat 22, .nat 99])) [] := by rfl
example : run [] 30 (.eval (.arraySet? (.var 0) (.nat 3) (.nat 99)) [sample] []) =
    .ret (.inl .unit) [] := by rfl
example : run [] 30 (initial (.arraySet? (.arrayEmpty .nat64) (.nat 0) (.nat 99))) =
    .ret (.inl .unit) [] := by rfl
example : run [] 50 (.eval
    (.pair (.arraySet? (.var 0) (.nat 1) (.nat 99)) (.var 0)) [sample] []) =
    .ret (.pair (.inr (.array [.nat 11, .nat 99, .nat 33])) sample) [] := by rfl
example : run [] 50 (.eval
    (.arraySet? (.var 0) (.letE (.nat 1) (.var 0)) (.var 1)) [sample, .nat 99] []) =
    .ret (.inr (.array [.nat 11, .nat 99, .nat 33])) [] := by rfl

-- Growth preserves element order, including when arrays contain arrays.
example : run [] 20 (initial (.arrayPush? (.arrayEmpty .nat64) (.nat 7))) =
    .ret (.inr (.array [.nat 7])) [] := by rfl
example : run [] 20 (.eval (.arrayPush? (.var 0) (.nat 44)) [sample] []) =
    .ret (.inr (.array [.nat 11, .nat 22, .nat 33, .nat 44])) [] := by rfl
example : run [] 20 (.eval (.arrayAppend? (.var 0) (.var 1))
    [sample, .array [.nat 44, .nat 55]] []) =
    .ret (.inr (.array [.nat 11, .nat 22, .nat 33, .nat 44, .nat 55])) [] := by rfl
example : run [] 20 (.eval (.arrayAppend? (.arrayEmpty .nat64) (.var 0)) [sample] []) =
    .ret (.inr sample) [] := by rfl
example : run [] 20 (.eval (.arrayAppend? (.var 0) (.arrayEmpty .nat64)) [sample] []) =
    .ret (.inr sample) [] := by rfl
example : run [] 20 (initial
    (.arrayPush? (.arrayEmpty (.array .nat64)) (.arrayEmpty .nat64))) =
    .ret (.inr (.array [.array []])) [] := by rfl

-- Even an invalid set evaluates its replacement before returning failure.
example : run [] 30 (initial
    (.arraySet? (.arrayEmpty .nat64) (.nat 0) overflowOne)) =
    .overflow .add largest 1 := by rfl
example : run [] 30 (initial
    (.arraySet? (.arrayEmpty .nat64) overflowOne overflowTwo)) =
    .overflow .add largest 1 := by rfl
example : run [] 30 (initial (.arrayGet?
    (.letE overflowOne (.arrayEmpty .nat64)) overflowTwo)) =
    .overflow .add largest 1 := by rfl
example : run [] 40 (initial (.arrayAppend?
    (.letE overflowOne (.arrayEmpty .nat64))
    (.letE overflowTwo (.arrayEmpty .nat64)))) = .overflow .add largest 1 := by rfl
example : run [] 30 (initial (.arrayPush? (.arrayEmpty .nat64) overflowTwo)) =
    .overflow .add largest 2 := by rfl

-- Admission visits every operand without shifting its lexical index.
example : uses 0 (.arraySet? (.var 2) (.var 1) (.var 0)) = true := by rfl
example : uses 1 (.arraySet? (.var 2) (.var 1) (.var 0)) = true := by rfl
example : uses 2 (.arraySet? (.var 2) (.var 1) (.var 0)) = true := by rfl
example : uses 3 (.arraySet? (.var 2) (.var 1) (.var 0)) = false := by rfl
example : admissible (.arrayPush? (.arrayEmpty .nat64) (.fst (.var 0))) = false := by rfl
example : admissible (.arraySet? (.var 0) (.nat 0) (.letE (.nat 1) (.nat 2))) =
    false := by rfl

-- Consume the Unit error payload explicitly and preserve success payload use.
def sizeAfterPush : Expr := .sumCase
  (.arrayPush? (.arrayEmpty .nat64) (.nat 7))
  (.unitCase (.var 0) (.nat 0)) (.arraySize (.var 0))

example : admissible sizeAfterPush = true := by rfl
example : run [] 50 (initial sizeAfterPush) = .ret (.nat 1) [] := by rfl
example : ProfileTyped [] [] [] sizeAfterPush .nat64 :=
  ⟨.sumCase (.arrayPush? (.arrayEmpty .nat64) (.nat (by decide)))
    (.unitCase (.var rfl) (.nat (by decide))) (.arraySize (.var rfl)), rfl⟩

-- Array parameters cross the same first-order call boundary as scalar values.
def sizeSignatures : Signatures := [⟨[.array .nat64], .nat64⟩]
def sizeProgram : Program := [.arraySize (.var 0)]

example : ProfileProgramTyped [] sizeProgram sizeSignatures :=
  ⟨⟨.nil, signaturesWellFormed_iff.mp rfl, .cons (.arraySize (.var rfl)) .nil⟩, rfl⟩
example : ProfileTyped [] sizeSignatures [] (.call 0 [.arrayEmpty .nat64]) .nat64 :=
  ⟨.call rfl (.cons (.arrayEmpty .nat64) .nil), rfl⟩
example : run sizeProgram 40 (.eval (.call 0 [.var 0]) [sample] []) =
    .ret (.nat 3) [] := by rfl

-- Typing rejects shape errors independently of the relevance check.
example : ¬ ExprTyped [] signatures Γ
    (.arrayPush? (.arrayEmpty .nat64) (.bool true)) τ := by
  intro typed
  cases typed with
  | arrayPush? arrayTyped itemTyped =>
      cases arrayTyped
      cases itemTyped

example : ¬ ExprTyped [] signatures Γ
    (.arrayGet? (.arrayEmpty .nat64) (.bool false)) τ := by
  intro typed
  cases typed with
  | arrayGet? _ indexTyped => cases indexTyped

example : ¬ ValueTyped [] (.array [.nat 1, .bool true]) (.array .nat64) := by
  intro typed
  cases typed with
  | array elements _ =>
      cases elements with
      | cons _ rest =>
          cases rest with
          | cons item _ => cases item

example : ¬ ValueTyped [] (.array [.nat nat64Limit]) (.array .nat64) := by
  intro typed
  cases typed with
  | array elements _ =>
      cases elements with
      | cons item _ =>
          cases item with
          | nat bounded => exact Nat.lt_irrefl _ bounded

-- Wrong operand shapes are stuck, never converted into an index/growth error.
example : Stuck [] (.ret .unit [.arraySize]) := by
  simp [Stuck, step, Terminal]
example : Stuck [] (.ret (.bool true) [.arrayGetIndex [.nat 1]]) := by
  simp [Stuck, step, Terminal]
example : Stuck [] (.ret (.nat 3) [.arrayAppendRight []]) := by
  simp [Stuck, step, Terminal]

end LeanExe.TypeSafety.ArrayTests
