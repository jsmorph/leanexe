import LeanExe.TypeSafety

/-!
Nominal declaration, construction, and matching regressions. These examples
check the specified binding/strictness boundaries; the general safety and
formation theorems remain independent of this bounded test runner.
-/

namespace LeanExe.TypeSafety.DataTests

def run (program : Program) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match step program state with
      | none => state
      | some next => run program fuel next

def pairDecls : DataDecls := [[[.nat64, .nat64]]]
def listDecls : DataDecls := [[[], [.nat64, .data 0]]]
def mutualDecls : DataDecls := [[[.nat64], [.data 1]], [[], [.data 0, .data 1]]]
def voidDecls : DataDecls := [[]]
def cyclicDecls : DataDecls := [[[.data 0]]]

-- Formation examines every constructor field and does not unfold recursion.
example : declarationsWellFormed [] = true := by rfl
example : declarationsWellFormed pairDecls = true := by rfl
example : declarationsWellFormed listDecls = true := by rfl
example : declarationsWellFormed mutualDecls = true := by rfl
example : declarationsWellFormed voidDecls = true := by rfl
example : declarationsWellFormed cyclicDecls = true := by rfl
example : declarationsWellFormed [[[.data 1]]] = false := by rfl
example : declarationsWellFormed [[[], [.array (.sum .unit (.data 1))]]] = false := by rfl
example : tyWellFormed [] (.data 0) = false := by rfl
example : tyWellFormed voidDecls (.data 0) = true := by rfl
example : tyWellFormed [] (.array (.data 0)) = false := by rfl
example : tyWellFormed [] (.sum .nat64 (.data 0)) = false := by rfl
example : signaturesWellFormed [] [⟨[.array (.data 0)], .nat64⟩] = false := by rfl
example : signaturesWellFormed [] [⟨[], .sum .unit (.data 0)⟩] = false := by rfl

example : DeclarationsWF listDecls := declarationsWellFormed_iff.mp rfl
example : DeclarationsWF mutualDecls := declarationsWellFormed_iff.mp rfl
example : ¬ TyWF [] (.data 0) := by
  intro formed
  cases formed with
  | data bounded => exact Nat.not_lt_zero _ bounded

-- Invalid internal types cannot disappear beneath an eliminator.
example : ¬ ExprTyped [] [] [] (.arraySize (.arrayEmpty (.data 0))) .nat64 := by
  intro typed
  cases typed with
  | arraySize arrayTyped =>
      cases arrayTyped with
      | arrayEmpty formed =>
          cases formed with
          | data bounded => exact Nat.not_lt_zero _ bounded

example : ¬ ExprTyped [] [] [] (.inl (.data 0) (.nat 7)) (.sum .nat64 (.data 0)) := by
  intro typed
  cases typed with
  | inl _ formed =>
      cases formed with
      | data bounded => exact Nat.not_lt_zero _ bounded

example : ¬ ValueTyped [] (.array []) (.array (.data 0)) := by
  intro typed
  cases typed with
  | array elements _ =>
      cases elements with
      | nil formed =>
          cases formed with
          | data bounded => exact Nat.not_lt_zero _ bounded

example : ¬ ExprTyped voidDecls [] [.data 0]
    (.dataCase 0 (.data 1) (.var 0) []) (.data 1) := by
  intro typed
  cases typed with
  | dataCase _ formed _ _ =>
      cases formed with
      | data bounded => exact (by decide : ¬ (1 < voidDecls.length)) bounded

-- Empty elimination is valid when its explicitly stated result type is valid.
example : ProfileTyped voidDecls [] [.data 0]
    (.dataCase 0 .nat64 (.var 0) []) .nat64 :=
  ⟨.dataCase rfl .nat64 (.var rfl) .nil, rfl⟩
example : ProfileTyped voidDecls [] [] (.arrayEmpty (.data 0)) (.array (.data 0)) :=
  ⟨.arrayEmpty (.data (by decide)), rfl⟩

example : ¬ ProgramTyped [] [.unit] [⟨[.data 0], .unit⟩] := by
  intro typed
  have checked := signaturesWellFormed_iff.mpr typed.signaturesWF
  change false = true at checked
  cases checked
example : ¬ ProgramTyped [[[.data 1]]] [.unit] [⟨[], .unit⟩] := by
  intro typed
  have checked := declarationsWellFormed_iff.mpr typed.declarationsWF
  change false = true at checked
  cases checked

-- Exact declared arity and complete branch coverage are typing obligations.
example : ¬ ExprTyped pairDecls [] [] (.dataCtor 0 0 [.nat 1]) (.data 0) := by
  intro typed
  cases typed with
  | dataCtor foundData foundCtor fields =>
      simp only [pairDecls, lookup, Option.some.injEq] at foundData
      cases foundData
      simp only [lookup, Option.some.injEq] at foundCtor
      cases foundCtor
      cases fields with
      | cons _ rest => cases rest

example : ¬ ExprTyped pairDecls [] [] (.dataCtor 0 1 []) (.data 0) := by
  intro typed
  cases typed with
  | dataCtor foundData foundCtor _ =>
      simp only [pairDecls, lookup, Option.some.injEq] at foundData
      cases foundData
      cases foundCtor

example : ¬ ExprTyped pairDecls [] [.data 0]
    (.dataCase 0 .nat64 (.var 0) []) .nat64 := by
  intro typed
  cases typed with
  | dataCase foundData _ _ branches =>
      simp only [pairDecls, lookup, Option.some.injEq] at foundData
      cases foundData
      cases branches

example : ¬ ExprTyped pairDecls [] [.data 0]
    (.dataCase 0 .nat64 (.var 0) [(1, .var 0)]) .nat64 := by
  intro typed
  cases typed with
  | dataCase foundData _ _ branches =>
      simp only [pairDecls, lookup, Option.some.injEq] at foundData
      cases foundData
      cases branches with
      | cons arity _ _ => cases arity

example : ¬ ExprTyped pairDecls [] [.data 0]
    (.dataCase 0 .nat64 (.var 0) [(2, .nat 0), (0, .nat 0)]) .nat64 := by
  intro typed
  cases typed with
  | dataCase foundData _ _ branches =>
      simp only [pairDecls, lookup, Option.some.injEq] at foundData
      cases foundData
      cases branches with
      | cons _ _ rest => cases rest

-- A valid declaration table can describe a type with no values.
example (value : Value) : ¬ ValueTyped voidDecls value (.data 0) := by
  intro typed
  obtain ⟨_, _, constructors, _, _, foundData, foundCtor, _⟩ := typed.data_canonical
  simp only [voidDecls, lookup, Option.some.injEq] at foundData
  cases foundData
  cases foundCtor

-- Strict construction preserves field order and captured environments.
example : run [] 20 (initial (.dataCtor 0 0 [])) =
    .ret (.data 0 0 []) [] := by rfl
example : run [] 30 (initial (.dataCtor 0 0 [.nat 11, .nat 22])) =
    .ret (.data 0 0 [.nat 11, .nat 22]) [] := by rfl
example : run [] 50 (initial (.letE (.nat 10)
    (.dataCtor 0 0 [.letE (.nat 20) (.var 0), .var 0]))) =
    .ret (.data 0 0 [.nat 20, .nat 10]) [] := by rfl

def largest : Nat := nat64Limit - 1
def overflowOne : Expr := .add (.nat largest) (.nat 1)
def overflowTwo : Expr := .add (.nat largest) (.nat 2)

-- Runtime terminal and continuation typing also require a formed result type.
example : ¬ StateTyped [] [] (.overflow largest 1) (.data 0) := by
  intro typed
  cases typed with
  | overflow _ _ _ formed =>
      cases formed with
      | data bounded => exact Nat.not_lt_zero _ bounded
example : ¬ KontTyped [] [] [] (.data 0) (.data 0) := by
  intro typed
  cases typed with
  | nil formed =>
      cases formed with
      | data bounded => exact Nat.not_lt_zero _ bounded

example : run [] 30 (initial (.dataCtor 0 0 [overflowOne, overflowTwo])) =
    .overflow largest 1 := by rfl

-- A complete two-field pattern binds field zero first, then field one.
def addFields : Expr := .dataCase 0 .nat64 (.dataCtor 0 0 [.nat 11, .nat 22])
  [(2, .add (.var 0) (.var 1))]

example : run [] 60 (initial addFields) = .ret (.nat 33) [] := by rfl
example : admissible addFields = true := by rfl
example : ProfileTyped pairDecls [] [] addFields .nat64 :=
  ⟨.dataCase rfl .nat64
    (.dataCtor rfl rfl (.cons (.nat (by decide)) (.cons (.nat (by decide)) .nil)))
    (.cons rfl (.add (.var rfl) (.var rfl)) .nil), rfl⟩
example : run [] 70 (initial (.letE (.nat 10)
    (.dataCase 0 .nat64 (.dataCtor 0 0 [.nat 2, .nat 3])
      [(2, .add (.var 0) (.add (.var 1) (.var 2)))]))) =
    .ret (.nat 15) [] := by rfl

-- Only the selected branch evaluates; every branch remains subject to typing.
example : run [] 40 (initial (.dataCase 0 .nat64 (.dataCtor 0 0 [])
    [(0, .nat 7), (0, overflowOne)])) = .ret (.nat 7) [] := by rfl
example : run [] 40 (initial (.dataCase 0 .nat64 (.dataCtor 0 1 [])
    [(0, overflowOne), (0, .nat 9)])) = .ret (.nat 9) [] := by rfl

-- Relevance uses the explicit branch arity for lexical shifts.
example : uses 0 (.dataCase 0 .nat64 (.dataCtor 0 0 []) [(2, .var 0)]) = false := by rfl
example : uses 0 (.dataCase 0 .nat64 (.dataCtor 0 0 []) [(2, .var 2)]) = true := by rfl
example : admissible (.dataCase 0 .nat64 (.dataCtor 0 0 [.nat 1, .nat 2])
    [(2, .var 0)]) = false := by rfl
example : admissible (.dataCase 0 .nat64 (.dataCtor 0 0 [.nat 1, .nat 2])
    [(2, .var 1)]) = false := by rfl
example : admissible (.dataCase 0 .nat64 (.dataCtor 0 0 []) [(0, .nat 7)]) = true := by rfl
example : admissible (.dataCtor 0 0 [.fst (.var 0)]) = false := by rfl

-- Malformed identity, missing branch, and wrong field arity are actual stuckness.
example : Stuck [] (run [] 30 (initial
    (.dataCase 1 .nat64 (.dataCtor 0 0 []) [(0, .nat 7)]))) := by
  change ((none : Option State) = none) ∧ ¬ False
  exact ⟨rfl, fun h => h⟩
example : Stuck [] (run [] 30 (initial
    (.dataCase 0 .nat64 (.dataCtor 0 1 []) [(0, .nat 7)]))) := by
  change ((none : Option State) = none) ∧ ¬ False
  exact ⟨rfl, fun h => h⟩
example : Stuck [] (run [] 30 (initial
    (.dataCase 0 .nat64 (.dataCtor 0 0 [.nat 1, .nat 2]) [(1, .var 0)]))) := by
  change ((none : Option State) = none) ∧ ¬ False
  exact ⟨rfl, fun h => h⟩
example : Stuck [] (run [] 30 (initial (.dataCase 0 .nat64 .unit []))) := by
  change ((none : Option State) = none) ∧ ¬ False
  exact ⟨rfl, fun h => h⟩

-- An ordinary recursive function can consume a recursive nominal value.
def sumProgram : Program := [.dataCase 0 .nat64 (.var 0)
  [(0, .nat 0), (2, .add (.var 0) (.call 0 [.var 1]))]]
def sumSignatures : Signatures := [⟨[.data 0], .nat64⟩]
def threeItems : Expr := .dataCtor 0 1 [.nat 3,
  .dataCtor 0 1 [.nat 5, .dataCtor 0 1 [.nat 7, .dataCtor 0 0 []]]]

example : run sumProgram 200 (initial (.call 0 [threeItems])) = .ret (.nat 15) [] := by rfl
example : programAdmissible sumProgram sumSignatures = true := by rfl

example : ProfileProgramTyped listDecls sumProgram sumSignatures :=
  ⟨⟨declarationsWellFormed_iff.mp rfl, signaturesWellFormed_iff.mp rfl,
    .cons (.dataCase rfl .nat64 (.var rfl)
      (.cons rfl (.nat (by decide))
        (.cons rfl (.add (.var rfl) (.call rfl (.cons (.var rfl) .nil))) .nil))) .nil⟩, rfl⟩

example : ProfileTyped listDecls sumSignatures [] (.call 0 [threeItems]) .nat64 :=
  ⟨.call rfl (.cons
    (.dataCtor rfl rfl (.cons (.nat (by decide)) (.cons
      (.dataCtor rfl rfl (.cons (.nat (by decide)) (.cons
        (.dataCtor rfl rfl (.cons (.nat (by decide)) (.cons
          (.dataCtor rfl rfl .nil) .nil))) .nil))) .nil))) .nil), rfl⟩

end LeanExe.TypeSafety.DataTests
