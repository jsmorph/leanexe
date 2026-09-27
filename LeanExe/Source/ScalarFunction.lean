import LeanExe.Source.ScalarPublicArgument
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
  | idResult (body : Arrow type 0 kind) :
      Arrow (.app (.const ``Id [.zero]) type) 0 kind
  | arg (rest : Arrow type arity kind) :
      Arrow (.forallE name (.const ``UInt64 []) type bi) (arity + 1) kind
  | booleanArg (rest : Arrow type arity kind) :
      Arrow (.forallE name (.const ``Bool []) type bi) (arity + 1) kind
  | metadata (body : Arrow type arity kind) : Arrow (.mdata data type) arity kind

theorem Arrow.inputs_length {type : Lean.Expr} {arity : Nat} {result : PublicResult}
    (signature : Arrow type arity result) : (publicInputs type).length = arity := by
  induction signature with
  | result kind => cases kind <;> rfl
  | idResult => rfl
  | arg _ ih => simp [publicInputs, ih]
  | booleanArg _ ih => simp [publicInputs, ih]
  | metadata _ ih => exact ih

/-- A source-only syntactic contract: concrete signature, lambda binders, and
an independently supported body. No compiler output occurs in this predicate. -/
def DeclarationSupported (type value : Lean.Expr) : Prop :=
  ∃ arity result body, Arrow type arity result ∧
    publicLambdasMatch (publicInputs type) value = true ∧
    LeanExe.Extract.Core.collectLambdas value arity = some body ∧
      (SupportedWith ((publicInputs type).reverse.map PublicArgument.kind) (result.encode body) ∨
        (publicInputs type = List.replicate arity .word ∧ result = .word ∧
          (RangeSupportedWith (List.replicate arity .word) body ∨
            Range.Exit.Supported (List.replicate arity .word) body)))

/-- Application of scalar arguments to the original elaborated lambda term.
The local environment is in de Bruijn order. -/
inductive Apply : Lean.Expr → List Value → List UInt64 → UInt64 → Prop where
  | done (body : EvalWith expr locals value) : Apply expr locals [] value
  | booleanDone (body : EvalWith (.app (.const ``Bool.toUInt64 []) expr) locals (Bool.toUInt64 flag)) :
      Apply expr locals [] (Bool.toUInt64 flag)
  | exit (body : Range.Exit.Eval expr locals value) : Apply expr locals [] value
  | lam (body : Apply expr (.word arg :: locals) args value) :
      Apply (.lam name (.const ``UInt64 []) expr bi) locals (arg :: args) value
  | booleanLam (body : Apply expr (.boolean (arg != 0) :: locals) args value) :
      Apply (.lam name (.const ``Bool []) expr bi) locals (arg :: args) value
  | metadata (body : Apply expr locals args value) :
      Apply (.mdata data expr) locals args value

theorem Apply.of_consumeMData {expr : Lean.Expr} {locals : List Value} {args : List UInt64} {value : UInt64}
    (h : Apply expr.consumeMData locals args value) : Apply expr locals args value := by
  induction expr with
  | mdata _ _ ih => exact .metadata (ih h)
  | _ => exact h

/-- Checked annotations fix the input decoding of each original lambda. -/
theorem apply_of_publicLambdas {expr body : Lean.Expr}
    (inputs : List PublicArgument) (args : List UInt64) (locals : List Value)
    (len : args.length = inputs.length)
    (annotations : publicLambdasMatch inputs expr = true)
    (collected : LeanExe.Extract.Core.collectLambdas expr args.length = some body)
    {value : UInt64}
    (semantics : Apply body ((publicValues inputs args).reverse ++ locals) [] value) :
    Apply expr locals args value := by
  induction args generalizing inputs expr locals with
  | nil =>
    cases inputs with
    | cons input inputs => simp at len
    | nil =>
      simp only [List.length_nil, LeanExe.Extract.Core.collectLambdas_zero,
        Option.some.injEq] at collected
      subst body
      exact semantics
  | cons arg args ih =>
    cases inputs with
    | nil => simp at len
    | cons input inputs =>
      have remaining : args.length = inputs.length := by simpa using len
      apply Apply.of_consumeMData
      simp only [List.length_cons, LeanExe.Extract.Core.collectLambdas] at collected
      split at collected
      · rename_i sourceHead name type inner bi heq
        rw [heq]
        simp only [publicLambdasMatch, heq, Bool.and_eq_true] at annotations
        obtain ⟨domainMatch, annotations⟩ := annotations
        have same := PublicArgument.matches_type domainMatch
        subst type
        have next := ih inputs (input.decode arg :: locals) remaining annotations collected
          (by simpa [publicValues, List.reverse_cons, List.append_assoc] using semantics)
        cases input with
        | word => exact .lam next
        | boolean => exact .booleanLam next
      · contradiction

/-- Typed public arguments are decoded before evaluating the original body. -/
theorem apply_typed_of_collectLambdas {expr body : Lean.Expr} (result : PublicResult)
    (inputs : List PublicArgument) (args : List UInt64) (locals : List Value)
    (len : args.length = inputs.length)
    (annotations : publicLambdasMatch inputs expr = true)
    (collected : LeanExe.Extract.Core.collectLambdas expr args.length = some body)
    {value : UInt64}
    (semantics : EvalWith (result.encode body) ((publicValues inputs args).reverse ++ locals) value) :
    Apply expr locals args value := by
  apply apply_of_publicLambdas inputs args locals len annotations collected
  cases result with
  | word => exact .done semantics
  | boolean =>
    obtain ⟨flag, rfl⟩ := semantics.booleanConversion_result
    exact .booleanDone semantics

/-- The all-word case retains its existing source evaluation. -/
theorem apply_of_collectLambdas {expr body : Lean.Expr} (args locals : List UInt64)
    (annotations : publicLambdasMatch (List.replicate args.length .word) expr = true)
    (collected : LeanExe.Extract.Core.collectLambdas expr args.length = some body)
    {value : UInt64} (semantics : Eval body (args.reverse ++ locals) value) :
    Apply expr (locals.map Value.word) args value := by
  apply apply_of_publicLambdas (List.replicate args.length .word) args (locals.map Value.word)
    (by simp) annotations collected
  apply Apply.done
  simpa [Eval, publicValues_words, List.map_reverse, List.map_append] using semantics

theorem apply_exit_of_collectLambdas {expr body : Lean.Expr} (args locals : List UInt64)
    (annotations : publicLambdasMatch (List.replicate args.length .word) expr = true)
    (collected : LeanExe.Extract.Core.collectLambdas expr args.length = some body)
    {value : UInt64} (semantics : Range.Exit.Eval body ((args.reverse ++ locals).map Value.word) value) :
    Apply expr (locals.map Value.word) args value := by
  apply apply_of_publicLambdas (List.replicate args.length .word) args (locals.map Value.word)
    (by simp) annotations collected
  apply Apply.exit
  simpa [Eval, publicValues_words, List.map_reverse, List.map_append] using semantics

end LeanExe.Source.Scalar
