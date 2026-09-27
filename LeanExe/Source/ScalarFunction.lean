import LeanExe.Source.ScalarRangeSupported
import LeanExe.Source.ScalarRangeExitSupported
import LeanExe.Extract.Syntax

namespace LeanExe.Source.Scalar

/-- Exported scalar result representation. Boolean results use zero or one. -/
inductive PublicResult where
  | word
  | boolean
  deriving DecidableEq, Repr

namespace PublicResult

def type : PublicResult → Lean.Expr
  | .word => .const ``UInt64 []
  | .boolean => .const ``Bool []

def encode (result : PublicResult) (body : Lean.Expr) : Lean.Expr :=
  match result with
  | .word => body
  | .boolean => .app (.const ``Bool.toUInt64 []) body

end PublicResult

inductive Arrow : Lean.Expr → Nat → PublicResult → Prop where
  | result (kind : PublicResult) : Arrow kind.type 0 kind
  | arg (rest : Arrow type arity kind) :
      Arrow (.forallE name (.const ``UInt64 []) type bi) (arity + 1) kind
  | metadata (body : Arrow type arity kind) : Arrow (.mdata data type) arity kind

/-- A source-only syntactic contract: concrete signature, lambda binders, and
an independently supported body. No compiler output occurs in this predicate. -/
def DeclarationSupported (type value : Lean.Expr) : Prop :=
  ∃ arity result body, Arrow type arity result ∧
    LeanExe.Extract.Core.collectLambdas value arity = some body ∧
      (Supported arity (result.encode body) ∨
        (result = .word ∧ (RangeSupportedWith (List.replicate arity .word) body ∨
          Range.Exit.Supported (List.replicate arity .word) body)))

/-- Application of scalar arguments to the original elaborated lambda term.
The local environment is in de Bruijn order. -/
inductive Apply : Lean.Expr → List UInt64 → List UInt64 → UInt64 → Prop where
  | done (body : Eval expr locals value) : Apply expr locals [] value
  | booleanDone (body : Eval (.app (.const ``Bool.toUInt64 []) expr) locals (Bool.toUInt64 flag)) :
      Apply expr locals [] (Bool.toUInt64 flag)
  | exit (body : Range.Exit.Eval expr (locals.map Value.word) value) : Apply expr locals [] value
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

/-- Boolean result application preserves the original term and exports its
proved zero-or-one encoding. -/
theorem apply_boolean_of_collectLambdas {expr body : Lean.Expr} (args locals : List UInt64)
    (collected : LeanExe.Extract.Core.collectLambdas expr args.length = some body)
    {flag : Bool} (semantics : Eval (.app (.const ``Bool.toUInt64 []) body)
      (args.reverse ++ locals) (Bool.toUInt64 flag)) :
    Apply expr locals args (Bool.toUInt64 flag) := by
  induction args generalizing expr locals with
  | nil =>
    simp only [List.length_nil, LeanExe.Extract.Core.collectLambdas_zero,
      Option.some.injEq] at collected
    subst body
    exact .booleanDone semantics
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

/-- Both supported public result kinds use the same encoded scalar body proof. -/
theorem apply_encoded_of_collectLambdas {expr body : Lean.Expr} (result : PublicResult)
    (args locals : List UInt64)
    (collected : LeanExe.Extract.Core.collectLambdas expr args.length = some body)
    {value : UInt64} (semantics : Eval (result.encode body) (args.reverse ++ locals) value) :
    Apply expr locals args value := by
  cases result with
  | word => exact apply_of_collectLambdas args locals collected semantics
  | boolean =>
    obtain ⟨flag, rfl⟩ := semantics.booleanConversion_result
    exact apply_boolean_of_collectLambdas args locals collected semantics

theorem apply_exit_of_collectLambdas {expr body : Lean.Expr} (args locals : List UInt64)
    (collected : LeanExe.Extract.Core.collectLambdas expr args.length = some body)
    {value : UInt64} (semantics : Range.Exit.Eval body ((args.reverse ++ locals).map Value.word) value) :
    Apply expr locals args value := by
  induction args generalizing expr locals with
  | nil =>
    simp only [List.length_nil, LeanExe.Extract.Core.collectLambdas_zero,
      Option.some.injEq] at collected
    subst body
    exact .exit semantics
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
