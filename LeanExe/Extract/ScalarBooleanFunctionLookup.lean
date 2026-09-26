import LeanExe.Extract.ScalarBindings
import LeanExe.Source.ScalarBooleanEnvironment

namespace LeanExe.Extract.Core

abbrev BooleanFunctionCompiler := LeanExe.IR.Expr → Option LeanExe.IR.Expr
abbrev BooleanFunctionLookup := Nat → Option BooleanFunctionCompiler

/-- Value bindings preserve outer function indices and install no function. -/
def BooleanFunctionLookup.shift (outer : BooleanFunctionLookup) : BooleanFunctionLookup
  | 0 => none
  | index + 1 => outer index

@[simp] theorem BooleanFunctionLookup.shift_zero (outer : BooleanFunctionLookup) : outer.shift 0 = none := rfl
@[simp] theorem BooleanFunctionLookup.shift_succ (outer : BooleanFunctionLookup) (index : Nat) :
    outer.shift (index + 1) = outer index := rfl

def BooleanFunctionLookup.Total (lookup : BooleanFunctionLookup) (indices : List Nat) : Prop :=
  ∀ index ∈ indices, ∃ function, lookup index = some function ∧ ∀ argument, ∃ target, function argument = some target

theorem BooleanFunctionLookup.Total.left {lookup : BooleanFunctionLookup} {left right : List Nat}
    (total : lookup.Total (left ++ right)) : lookup.Total left :=
  fun index member => total index (List.mem_append_left _ member)

theorem BooleanFunctionLookup.Total.right {lookup : BooleanFunctionLookup} {left right : List Nat}
    (total : lookup.Total (left ++ right)) : lookup.Total right :=
  fun index member => total index (List.mem_append_right _ member)

theorem BooleanFunctionLookup.Total.shift {lookup : BooleanFunctionLookup} {indices : List Nat}
    (total : lookup.Total (LeanExe.Source.Scalar.booleanLetVariables indices))
    (noLocal : 0 ∉ indices) : lookup.shift.Total indices := by
  intro index member
  cases index with
  | zero => exact False.elim (noLocal member)
  | succ index => exact total index ((LeanExe.Source.Scalar.mem_booleanLetVariables indices index).mpr member)

/-- Every referenced function must be available in the lexical environment. -/
def BooleanFunctionLookup.Present (lookup : BooleanFunctionLookup) (indices : List Nat) : Prop :=
  ∀ index ∈ indices, ∃ function, lookup index = some function

theorem BooleanFunctionLookup.Present.no_local {lookup : BooleanFunctionLookup} {indices : List Nat}
    (present : lookup.shift.Present indices) : 0 ∉ indices := by
  intro member
  obtain ⟨function, found⟩ := present 0 member
  cases found

theorem BooleanFunctionLookup.Present.external {lookup : BooleanFunctionLookup} {indices : List Nat}
    (present : lookup.shift.Present indices) :
    lookup.Present (LeanExe.Source.Scalar.booleanLetVariables indices) := by
  intro index member
  exact present (index + 1) ((LeanExe.Source.Scalar.mem_booleanLetVariables indices index).mp member)

def BooleanFunctionLookup.Meaning (lookup : BooleanFunctionLookup) (indices : List Nat)
    (native : Nat → UInt64 → Bool) (store : LeanExe.IR.ScalarStore) : Prop :=
  ∀ index ∈ indices, ∀ function, lookup index = some function →
    ∀ argument value target, argument.ScalarEval store value store → function argument = some target →
      target.ScalarEval store (Bool.toUInt64 (native index value)) store

def BooleanFunctionLookup.Holds (lookup : BooleanFunctionLookup) (indices : List Nat)
    (P : LeanExe.IR.Expr → Prop) : Prop :=
  ∀ index ∈ indices, ∀ function, lookup index = some function →
    ∀ argument target, P argument → function argument = some target → P target

theorem BooleanFunctionLookup.Meaning.left {lookup : BooleanFunctionLookup}
    {left right : List Nat} {native store} (meaning : lookup.Meaning (left ++ right) native store) :
    lookup.Meaning left native store :=
  fun index member => meaning index (List.mem_append_left _ member)

theorem BooleanFunctionLookup.Meaning.right {lookup : BooleanFunctionLookup}
    {left right : List Nat} {native store} (meaning : lookup.Meaning (left ++ right) native store) :
    lookup.Meaning right native store :=
  fun index member => meaning index (List.mem_append_right _ member)

theorem BooleanFunctionLookup.Meaning.shift {lookup : BooleanFunctionLookup} {indices : List Nat}
    {native : LeanExe.Source.Scalar.BooleanEnvironment} {store} (flag : Bool)
    (meaning : lookup.Meaning (LeanExe.Source.Scalar.booleanLetVariables indices) native.predicates store) :
    lookup.shift.Meaning indices (native.bind flag).predicates store := by
  intro index member function found
  cases index with
  | zero => cases found
  | succ index =>
      exact meaning index ((LeanExe.Source.Scalar.mem_booleanLetVariables indices index).mpr member) function found

theorem BooleanFunctionLookup.Holds.left {lookup : BooleanFunctionLookup}
    {left right : List Nat} {P} (holds : lookup.Holds (left ++ right) P) : lookup.Holds left P :=
  fun index member => holds index (List.mem_append_left _ member)

theorem BooleanFunctionLookup.Holds.right {lookup : BooleanFunctionLookup}
    {left right : List Nat} {P} (holds : lookup.Holds (left ++ right) P) : lookup.Holds right P :=
  fun index member => holds index (List.mem_append_right _ member)

theorem BooleanFunctionLookup.Holds.shift {lookup : BooleanFunctionLookup} {indices : List Nat} {P}
    (holds : lookup.Holds (LeanExe.Source.Scalar.booleanLetVariables indices) P) :
    lookup.shift.Holds indices P := by
  intro index member function found
  cases index with
  | zero => cases found
  | succ index =>
      exact holds index ((LeanExe.Source.Scalar.mem_booleanLetVariables indices index).mpr member) function found

end LeanExe.Extract.Core
