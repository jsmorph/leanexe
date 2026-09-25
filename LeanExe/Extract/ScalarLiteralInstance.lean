import LeanExe.Source.ScalarLiteralInstance

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Recognize only a standard numeral instance behind a constant function spine.
Tracking unapplied arguments rejects both an uncalled lambda and an overapplication. -/
def literalInstance? (number : Nat) : Lean.Expr → Nat → Bool
  | .app (.const ``UInt64.instOfNat []) (.lit (.natVal found)), arity =>
      number == found && arity == 0
  | .app function _, arity => literalInstance? number function (arity + 1)
  | .lam _ _ body _, arity + 1 => literalInstance? number body arity
  | .letE _ _ _ body _, arity => literalInstance? number body arity
  | .mdata _ body, arity => literalInstance? number body arity
  | _, _ => false

theorem literalInstance_sound {number expression arity}
    (accepted : literalInstance? number expression arity = true) :
    LiteralInstance number arity expression := by
  induction expression, arity using literalInstance?.induct with
  | case1 found arity =>
    simp only [literalInstance?, Bool.and_eq_true, beq_iff_eq] at accepted
    rcases accepted with ⟨rfl, rfl⟩
    exact .standard
  | case2 function argument arity excluded ih =>
    rw [literalInstance?] at accepted
    · exact .apply (ih accepted)
    · exact excluded
  | case3 name type body bi arity ih =>
    exact .lambda (ih accepted)
  | case4 name type value body nondep arity ih => exact .letE (ih accepted)
  | case5 data body arity ih => exact .metadata (ih accepted)
  | case6 expression arity excludedApp excludedLam excludedLet excludedMetadata =>
    rw [literalInstance?] at accepted <;> first | assumption | contradiction

theorem literalInstance_accepts {number arity expression}
    (evidence : LiteralInstance number arity expression) :
    literalInstance? number expression arity = true := by
  induction evidence with
  | standard => simp [literalInstance?]
  | lambda body ih => exact ih
  | apply function ih =>
    rw [literalInstance?]
    · exact ih
    · intro found same _
      cases same
      exact function.not_const _ _ rfl
  | letE body ih => exact ih
  | metadata body ih => exact ih

end LeanExe.Extract.Core
