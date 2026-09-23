import LeanExe.TypeSafety

/-!
Boundary checks for strict evaluation and the syntactic relevance profile.
The finite runner supplies concrete traces; universal safety is proved in the
library. Admissibility and ordinary typing are tested as separate obligations.
-/

namespace LeanExe.TypeSafety.ProfileTests

def run (program : Program) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match step program state with
      | none => state
      | some next => run program fuel next

def largest : Nat := nat64Limit - 1
def overflow : Expr := .add (.nat largest) (.nat 1)

-- Product patterns bind both fields in their documented order.
def addPair : Expr := .split (.pair (.nat 11) (.nat 22)) (.add (.var 0) (.var 1))

example : run [] 30 (initial addPair) = .ret (.nat 33) [] := by rfl
example : admissible addPair = true := by rfl
example : ProfileTyped [] [] [] addPair .nat64 :=
  ⟨.split (.pair (.nat (by decide)) (.nat (by decide)))
    (.add (.var rfl) (.var rfl)), rfl⟩

-- A pattern and an inner let preserve the surrounding lexical environment.
example : run [] 40 (initial (.letE (.nat 10)
    (.split (.pair (.nat 2) (.nat 3))
      (.letE (.nat 4) (.add (.var 0) (.add (.var 1) (.add (.var 2) (.var 3)))))))) =
    .ret (.nat 19) [] := by rfl

-- Unit elimination consumes its constructor without inventing a field binder.
example : run [] 20 (initial (.unitCase .unit (.nat 9))) = .ret (.nat 9) [] := by rfl
example : ProfileTyped [] [] [] (.unitCase .unit (.nat 9)) .nat64 :=
  ⟨.unitCase .unit (.nat (by decide)), rfl⟩

example : ProfileTyped [] [] []
    (.sumCase (.inl .unit)
      (.unitCase (.var 0) (.nat 7)) (.unitCase (.var 0) (.nat 9))) .nat64 :=
  ⟨.sumCase (.inl .unit .unit) (.unitCase (.var rfl) (.nat (by decide)))
    (.unitCase (.var rfl) (.nat (by decide))), rfl⟩

-- Strictness remains explicit even for a term rejected by the profile.
example : run [] 30 (initial (.letE overflow (.nat 7))) = .overflow largest 1 := by rfl
example : admissible (.letE overflow (.nat 7)) = false := by rfl
example : run [] 40 (initial
    (.split (.pair (.nat 7) overflow) (.add (.var 0) (.var 1)))) =
    .overflow largest 1 := by rfl

-- Missing a pattern use is rejected, including through a nested binding.
example : admissible (.split (.pair (.nat 1) (.nat 2)) (.var 0)) = false := by rfl
example : admissible (.split (.pair (.nat 1) (.nat 2)) (.var 1)) = false := by rfl
example : admissible (.letE (.nat 1) (.letE (.nat 2) (.var 0))) = false := by rfl
example : admissible (.sumCase (.inl (.nat 1)) (.nat 7) (.var 0)) = false := by rfl
example : admissible (.sumCase (.inr (.nat 1)) (.var 0) (.nat 7)) = false := by rfl

-- Projections are rejected recursively, not only on visible pair literals.
example : admissible (.fst (.var 0)) = false := by rfl
example : admissible (.snd (.var 0)) = false := by rfl
example : admissible (.call 0 [.pair (.nat 1) (.fst (.var 0))]) = false := by rfl

-- Correct de Bruijn shifts distinguish an inner binder from an outer variable.
example : uses 0 (.letE (.nat 1) (.var 0)) = false := by rfl
example : uses 0 (.letE (.nat 1) (.var 1)) = true := by rfl
example : uses 0 (.split (.pair .unit .unit) (.var 0)) = false := by rfl
example : uses 0 (.split (.pair .unit .unit) (.var 1)) = false := by rfl
example : uses 0 (.split (.pair .unit .unit) (.var 2)) = true := by rfl
example : uses 0 (.sumCase (.inl .unit) (.var 0) (.var 0)) = false := by rfl
example : uses 0 (.sumCase (.inl .unit) (.var 1) (.var 0)) = true := by rfl
example : uses 0 (.unitCase .unit (.var 0)) = true := by rfl

-- Syntactic occurrence permits duplication and does not assert all-path use.
example : admissible (.letE (.nat 5) (.add (.var 0) (.var 0))) = true := by rfl
example : run [] 30 (initial (.letE (.nat 5) (.add (.var 0) (.var 0)))) =
    .ret (.nat 10) [] := by rfl
example : admissible (.letE (.nat 5) (.ifE (.bool false) (.var 0) (.nat 0))) =
    true := by rfl
example : run [] 30 (initial
    (.letE (.nat 5) (.ifE (.bool false) (.var 0) (.nat 0)))) = .ret (.nat 0) [] := by rfl

-- Every function parameter is checked, independently of call-site arguments.
def signatures : Signatures := [⟨[.prod .nat64 .nat64], .nat64⟩]
def program : Program := [.split (.var 0) (.add (.var 0) (.var 1))]

example : ProfileProgramTyped [] program signatures :=
  ⟨⟨.nil, signaturesWellFormed_iff.mp rfl,
    .cons (.split (.var rfl) (.add (.var rfl) (.var rfl))) .nil⟩, rfl⟩
example : ProfileTyped [] signatures [] (.call 0 [.pair (.nat 4) (.nat 5)]) .nat64 :=
  ⟨.call rfl (.cons (.pair (.nat (by decide)) (.nat (by decide))) .nil), rfl⟩
example : run program 40 (initial (.call 0 [.pair (.nat 4) (.nat 5)])) =
    .ret (.nat 9) [] := by rfl
example : programAdmissible [.nat 7] [⟨[.nat64], .nat64⟩] = false := by rfl
example : programAdmissible [.letE (.nat 1) (.var 0)] [⟨[.nat64], .nat64⟩] =
    false := by rfl
example : programAdmissible [] [⟨[], .unit⟩] = false := by rfl
example : programAdmissible [.unit] [] = false := by rfl

-- A passed occurrence check is not evidence of typing.
example : admissible (.var 99) = true := by rfl
example : ¬ ProfileTyped [] [] [] (.var 99) τ := by
  rintro ⟨typed, _⟩
  cases typed with
  | var found => simp [lookup] at found

-- Malformed eliminations remain stuck, not permitted failures.
example : Stuck [] (.ret (.nat 3) [.unitBody (.nat 9) []]) := by
  simp [Stuck, step, Terminal]
example : Stuck [] (.ret .unit [.splitBody (.var 0) []]) := by
  simp [Stuck, step, Terminal]

end LeanExe.TypeSafety.ProfileTests
