import LeanExe.TypeSafety

/-!
Semantic regression examples for the independent core. These checks exercise
binding, strictness, failure identity, and call boundaries in addition to the
universal safety proofs. The bounded runner below is a test helper, not the
definition of the core semantics or a termination claim.
-/

namespace LeanExe.TypeSafety.Tests

def run (program : Program) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match step program state with
      | none => state
      | some next => run program fuel next

def largest : Nat := nat64Limit - 1
def overflowOne : Expr := .add (.nat largest) (.nat 1)
def overflowTwo : Expr := .add (.nat largest) (.nat 2)

-- Captured environments survive an inner binding in the left component.
example : run [] 30 (initial
    (.letE (.nat 10) (.pair (.letE (.nat 20) (.var 0)) (.var 0)))) =
    .ret (.pair (.nat 20) (.nat 10)) [] := by rfl

-- Each sum branch binds its payload in front of its lexical environment.
example : run [] 30 (initial
    (.letE (.nat 10) (.sumCase (.inl (.nat 7))
      (.add (.var 0) (.var 1)) (.nat 0)))) = .ret (.nat 17) [] := by rfl

example : run [] 30 (initial
    (.letE (.nat 10) (.sumCase (.inr (.nat 7))
      (.nat 0) (.add (.var 0) (.var 1))))) = .ret (.nat 17) [] := by rfl

-- An unselected branch is not evaluated.
example : run [] 20 (initial (.ifE (.bool true) (.nat 7) overflowOne)) =
    .ret (.nat 7) [] := by rfl

example : run [] 20 (initial (.ifE (.bool false) overflowOne (.nat 7))) =
    .ret (.nat 7) [] := by rfl

-- The core specifies strict pairs, even when the result is projected.
example : run [] 30 (initial (.fst (.pair (.nat 7) overflowOne))) =
    .overflow largest 1 := by rfl

-- The natural boundary is checked, not wrapped modulo 2^64.
example : run [] 20 (initial (.add (.nat largest) (.nat 0))) =
    .ret (.nat largest) [] := by rfl

example : run [] 20 (initial overflowOne) = .overflow largest 1 := by rfl

example : ExprTyped [] [] [] overflowOne .nat64 :=
  .add (.nat (by decide)) (.nat (by decide))

example : ¬ ExprTyped [] signatures Γ (.nat nat64Limit) .nat64 := by
  intro typed
  cases typed with
  | nat bounded => exact Nat.lt_irrefl _ bounded

-- Ill-shaped execution is genuinely stuck and cannot be labeled overflow.
example : Stuck [] (initial (.var 0)) := by
  simp [Stuck, initial, step, lookup, Terminal]

example : Stuck [] (.ret (.nat 3) [.fst]) := by
  simp [Stuck, step, Terminal]

example : Stuck [] (.ret (.nat 3) [.ifBranches .unit .unit []]) := by
  simp [Stuck, step, Terminal]

example : ¬ Terminal (.overflow 1 1) := by
  unfold Terminal
  decide

-- Parameter index zero is the first argument; calls use a fresh environment.
def pairSignatures : Signatures := [⟨[.nat64, .nat64], .prod .nat64 .nat64⟩]
def pairProgram : Program := [.pair (.var 0) (.var 1)]

example : ProgramTyped [] pairProgram pairSignatures :=
  ⟨.nil, signaturesWellFormed_iff.mp rfl, .cons (.pair (.var rfl) (.var rfl)) .nil⟩

example : ExprTyped [] pairSignatures [] (.call 0 [.nat 11, .nat 22])
    (.prod .nat64 .nat64) :=
  .call rfl (.cons (.nat (by decide)) (.cons (.nat (by decide)) .nil))

example : run pairProgram 30 (initial (.call 0 [.nat 11, .nat 22])) =
    .ret (.pair (.nat 11) (.nat 22)) [] := by rfl

-- The caller environment is restored for the continuation after a callee.
example : run pairProgram 50 (initial (.letE (.nat 99)
    (.pair (.call 0 [.nat 11, .nat 22]) (.var 0)))) =
    .ret (.pair (.pair (.nat 11) (.nat 22)) (.nat 99)) [] := by rfl

-- Argument failures identify left-to-right evaluation, even for unused arguments.
example : run [.nat 9] 40 (initial (.call 0 [overflowOne, overflowTwo])) =
    .overflow largest 1 := by rfl

example : run [.nat 9] 20 (initial (.call 0 [])) = .ret (.nat 9) [] := by rfl

example : Stuck [] (initial (.call 0 [])) := by
  simp [Stuck, initial, step, enterCall, lookup, Terminal]

-- A malformed callee cannot capture a caller local accidentally.
example : run [.var 0] 20 (initial (.letE (.nat 99) (.call 0 []))) =
    .eval (.var 0) [] [] := by rfl

example : ¬ ExprTyped [] pairSignatures [] (.call 0 []) (.prod .nat64 .nat64) := by
  intro typed
  cases typed with
  | call found arguments =>
      cases arguments
      simp [pairSignatures, lookup] at found

-- A well-typed recursive call is safe without assuming it terminates.
def recursiveSignatures : Signatures := [⟨[], .unit⟩]
def recursiveProgram : Program := [.call 0 []]

example : ProgramTyped [] recursiveProgram recursiveSignatures :=
  ⟨.nil, signaturesWellFormed_iff.mp rfl, .cons (.call rfl .nil) .nil⟩

example : ExprTyped [] recursiveSignatures [] (.call 0 []) .unit := .call rfl .nil

example : Step recursiveProgram (initial (.call 0 [])) (initial (.call 0 [])) := rfl

end LeanExe.TypeSafety.Tests
