import LeanExe.Source.ScalarBooleanWordRange
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
  | arg (input : PublicArgument.Domain kind domain) (rest : Arrow type arity result) :
      Arrow (.forallE name domain type bi) (arity + 1) result
  | metadata (body : Arrow type arity kind) : Arrow (.mdata data type) arity kind

theorem Arrow.inputs_length {type : Lean.Expr} {arity : Nat} {result : PublicResult}
    (signature : Arrow type arity result) : (publicInputs type).length = arity := by
  induction signature with
  | result kind => cases kind <;> rfl
  | idResult => rfl
  | arg input _ ih => simp [publicInputs, PublicArgument.ofType_accepts input, ih]
  | metadata _ ih => exact ih

/-- A source-only syntactic contract: concrete signature, lambda binders, and
an independently supported body. No compiler output occurs in this predicate. -/
def DeclarationSupported (type value : Lean.Expr) : Prop :=
  ∃ arity result body, Arrow type arity result ∧
    publicLambdasMatch (publicInputs type) value = true ∧
    LeanExe.Extract.Core.collectLambdas value arity = some body ∧
      (SupportedWith ((publicInputs type).reverse.map PublicArgument.kind) (result.encode body) ∨
        (result = .word ∧
          (RangeSupportedWith ((publicInputs type).reverse.map PublicArgument.kind) body ∨
            Range.Exit.Supported ((publicInputs type).reverse.map PublicArgument.kind) body)) ∨
        (result = .boolean ∧ BooleanRange.Supported ((publicInputs type).reverse.map PublicArgument.kind) body) ∨
        (result = .word ∧ BooleanWordRange.Supported ((publicInputs type).reverse.map PublicArgument.kind) body))

/-- Application of scalar arguments to the original elaborated lambda term.
The local environment is in de Bruijn order. -/
inductive Apply : Lean.Expr → List Value → List UInt64 → UInt64 → Prop where
  | done (body : EvalWith expr locals value) : Apply expr locals [] value
  | booleanDone (body : EvalWith (.app (.const ``Bool.toUInt64 []) expr) locals (Bool.toUInt64 flag)) :
      Apply expr locals [] (Bool.toUInt64 flag)
  | booleanRangeDone (body : BooleanRange.Eval expr locals flag) :
      Apply expr locals [] flag.toUInt64
  | booleanWordRangeDone (body : BooleanWordRange.Eval expr locals value) : Apply expr locals [] value
  | exit (body : Range.Exit.Eval expr locals value) : Apply expr locals [] value
  | lam (body : Apply expr (.word arg :: locals) args value) :
      Apply (.lam name (.const ``UInt64 []) expr bi) locals (arg :: args) value
  | booleanLam (body : Apply expr (.boolean (arg != 0) :: locals) args value) :
      Apply (.lam name (.const ``Bool []) expr bi) locals (arg :: args) value
  | idLam (body : Apply (.lam name domain expr bi) locals args value) :
      Apply (.lam name (.app (.const ``Id [.zero]) domain) expr bi) locals args value
  | metadata (body : Apply expr locals args value) :
      Apply (.mdata data expr) locals args value

theorem Apply.typedLam {input : PublicArgument} {domain expr : Lean.Expr}
    {name : Lean.Name} {bi : Lean.BinderInfo} {locals : List Value} {arg : UInt64}
    {args : List UInt64} {value : UInt64}
    (valid : PublicArgument.Domain input domain)
    (body : Apply expr (input.decode arg :: locals) args value) :
    Apply (.lam name domain expr bi) locals (arg :: args) value := by
  induction valid with
  | word => exact .lam body
  | boolean => exact .booleanLam body
  | identity _ ih => exact .idLam (ih body)

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
        have next := ih inputs (input.decode arg :: locals) remaining annotations collected
          (by simpa [publicValues, List.reverse_cons, List.append_assoc] using semantics)
        exact Apply.typedLam (PublicArgument.acceptsType_domain domainMatch) next
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
