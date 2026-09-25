import LeanExe.Source.ScalarRangeSupported
import LeanExe.Extract.Syntax

namespace LeanExe.Source.Scalar

inductive Arrow : Lean.Expr → Nat → Prop where
  | result : Arrow (.const ``UInt64 []) 0
  | arg (rest : Arrow type arity) :
      Arrow (.forallE name (.const ``UInt64 []) type bi) (arity + 1)
  | metadata (body : Arrow type arity) : Arrow (.mdata data type) arity

/-- A source-only syntactic contract: concrete signature, lambda binders, and
an independently supported body. No compiler output occurs in this predicate. -/
def DeclarationSupported (type value : Lean.Expr) : Prop :=
  ∃ arity body, Arrow type arity ∧
    LeanExe.Extract.Core.collectLambdas value arity = some body ∧
      (Supported arity body ∨ RangeSupportedWith (List.replicate arity .word) body)

/-- Application of scalar arguments to the original elaborated lambda term.
The local environment is in de Bruijn order. -/
inductive Apply : Lean.Expr → List UInt64 → List UInt64 → UInt64 → Prop where
  | done (body : Eval expr locals value) : Apply expr locals [] value
  | lam (body : Apply expr (arg :: locals) args value) :
      Apply (.lam name type expr bi) locals (arg :: args) value
  | metadata (body : Apply expr locals args value) :
      Apply (.mdata data expr) locals args value

theorem Apply.of_consumeMData {expr : Lean.Expr} {locals args : List UInt64} {value : UInt64}
    (h : Apply expr.consumeMData locals args value) : Apply expr locals args value := by
  induction expr with
  | mdata _ _ ih => exact .metadata (ih h)
  | _ => exact h

/-- Removing lambda binders and reversing the argument environment implements
the source application relation; the original term remains in the conclusion. -/
theorem apply_of_collectLambdas {expr body : Lean.Expr} (args locals : List UInt64)
    (collected : LeanExe.Extract.Core.collectLambdas expr args.length = some body)
    {value : UInt64} (semantics : Eval body (args.reverse ++ locals) value) :
    Apply expr locals args value := by
  induction args generalizing expr locals with
  | nil =>
    simp only [List.length_nil, LeanExe.Extract.Core.collectLambdas_zero,
      Option.some.injEq] at collected
    subst body
    exact .done semantics
  | cons arg args ih =>
    apply Apply.of_consumeMData
    simp only [List.length_cons, LeanExe.Extract.Core.collectLambdas] at collected
    split at collected
    · rename_i sourceHead name type inner bi heq
      rw [heq]
      apply Apply.lam
      apply ih _ collected
      simpa [List.reverse_cons, List.append_assoc] using semantics
    · contradiction

end LeanExe.Source.Scalar
