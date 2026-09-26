import LeanExe.Source.ScalarTypedLiteralInstance
import LeanExe.Source.ExprEquality
import LeanExe.Extract.ScalarLiteralInstance

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def typedLiteralInstance? (number : Nat) : ResultType → Lean.Expr → Bool
  | .word, evidence => literalInstance? number evidence 0
  | .identity inner, expression =>
      match expression with
      | .app (.app (.app (.const ``Id.instOfNat [.zero]) type) numeral) evidence =>
          LeanExe.Source.ExprEquality.same type inner.expr && naturalLiteral? numeral == some number &&
            typedLiteralInstance? number inner evidence
      | _ => false

theorem typedLiteralInstance_accepts {number type expression}
    (evidence : TypedLiteralInstance number type expression) :
    typedLiteralInstance? number type expression = true := by
  induction evidence with
  | word evidence => exact literalInstance_accepts evidence
  | identity type numeral evidence ih =>
    simp [typedLiteralInstance?, naturalLiteral_accepts numeral, ih]

theorem typedLiteralInstance_sound {number type expression}
    (accepted : typedLiteralInstance? number type expression = true) :
    TypedLiteralInstance number type expression := by
  induction type generalizing expression with
  | word => exact .word (literalInstance_sound accepted)
  | identity inner ih =>
    simp only [typedLiteralInstance?] at accepted
    split at accepted
    · simp only [Bool.and_eq_true, beq_iff_eq] at accepted
      obtain ⟨⟨same, numeral⟩, evidence⟩ := accepted
      have typeShape := LeanExe.Source.ExprEquality.same_eq_true.mp same
      rw [typeShape]
      exact .identity inner (naturalLiteral_sound numeral) (ih evidence)
    · contradiction

end LeanExe.Extract.Core
