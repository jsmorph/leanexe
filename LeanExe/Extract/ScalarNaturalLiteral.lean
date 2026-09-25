import LeanExe.Source.ScalarNaturalLiteral

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def naturalType? : Lean.Expr → Bool
  | .const ``Nat [] => true
  | .mdata _ type => naturalType? type
  | _ => false

theorem naturalType_accepts {type} (supported : NaturalType type) : naturalType? type = true := by
  induction supported with
  | natural => rfl
  | metadata _ ih => exact ih

theorem naturalType_sound {type} (accepted : naturalType? type = true) : NaturalType type := by
  induction type using naturalType?.induct with
  | case1 => exact .natural
  | case2 data type ih => exact .metadata (ih accepted)
  | case3 type noNat noMetadata =>
    rw [naturalType?] at accepted <;> first | assumption | contradiction

/-- Preserve exact numeral syntax while reading its native Nat value. -/
def naturalLiteral? : Lean.Expr → Option Nat
  | .lit (.natVal number) => some number
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) type) (.lit (.natVal number)))
      (.app (.const ``instOfNatNat []) (.lit (.natVal found))) =>
      if number == found && naturalType? type then some number else none
  | .mdata _ value => naturalLiteral? value
  | _ => none

theorem naturalLiteral_accepts {number expression} (literal : NaturalLiteral number expression) :
    naturalLiteral? expression = some number := by
  induction literal with
  | raw => rfl
  | ofNat type => simp [naturalLiteral?, naturalType_accepts type]
  | metadata _ ih => exact ih

theorem naturalLiteral_sound {number expression} (accepted : naturalLiteral? expression = some number) :
    NaturalLiteral number expression := by
  induction expression using naturalLiteral?.induct with
  | case1 found => cases accepted; exact .raw
  | case2 type candidate found same =>
    simp only [Bool.and_eq_true, beq_iff_eq] at same
    rcases same with ⟨rfl, ht⟩
    simp only [naturalLiteral?, ht, beq_self_eq_true, Bool.and_self, ↓reduceIte, Option.some.injEq] at accepted
    subst number
    exact .ofNat (naturalType_sound ht)
  | case3 type candidate found rejected =>
    simp [naturalLiteral?, rejected] at accepted
  | case4 data expression ih => exact .metadata (ih accepted)
  | case5 expression noLiteral noOfNat noMetadata =>
    rw [naturalLiteral?] at accepted <;> first | assumption | contradiction

end LeanExe.Extract.Core
