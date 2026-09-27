import LeanExe.Extract.ScalarBooleanSequenceCorrectness
import LeanExe.Extract.ScalarSequenceCorrectness
import LeanExe.Extract.ScalarRangeCorrectness
import LeanExe.Extract.ScalarRangeExitCorrectness
import LeanExe.Extract.ScalarSignature
import LeanExe.Extract.ScalarPublicBindings

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (PublicArgument publicInputs publicValues publicLambdasMatch)

def scalarFunc (name : Lean.Name) (exportName : Option String) (arity : Nat)
    (expression : LeanExe.IR.Expr) : LeanExe.IR.Func :=
  { sourceName := name
    exportName
    params := arity
    locals := arity + 1
    body := .assign arity expression
    results := [.local arity] }

/-- The scalar declaration case, using the existing IR and result-slot ABI. -/
def extractScalarFunc (name : Lean.Name) (exportName : Option String)
    (type value : Lean.Expr) : Option LeanExe.IR.Func := do
  let (arity, result) ← scalarSignature? type
  if !publicLambdasMatch (publicInputs type) value then none else do
  let body ← collectLambdas value arity
  match extractScalarExprWith (publicBindings (publicInputs type)) (result.encode body) with
  | some expression => pure (scalarFunc name exportName arity expression)
  | none =>
      match result with
      | .boolean =>
          match extractScalarBooleanRangeWith (publicBindings (publicInputs type)) arity body with
          | some plan => pure (plan.func name exportName arity)
          | none => do
              let plan ← extractScalarBooleanSequenceWith (publicBindings (publicInputs type)) arity body
              pure (plan.func name exportName arity)
      | .word => do
          let locals := publicBindings (publicInputs type)
          match extractScalarRangeWith locals arity body with
          | some plan => pure (plan.func name exportName arity)
          | none =>
              match extractScalarRangeExitWith locals arity body with
              | some plan => pure (plan.func name exportName arity)
              | none =>
                  match extractScalarWordRangeWith locals arity body with
                  | some plan => pure (plan.func name exportName arity)
                  | none => do
                      let plan ← extractScalarSequenceWith locals arity body
                      pure (plan.func name exportName arity)

/-- Successful extraction selects a pure expression or a checked range result.
The original signature and lambda binders determine the result encoding. -/
theorem extractScalarFunc_cases {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name exportName type source = some func) :
    ∃ arity result body, scalarSignature? type = some (arity, result) ∧
      publicLambdasMatch (publicInputs type) source = true ∧
      collectLambdas source arity = some body ∧
      ((∃ expression, extractScalarExprWith (publicBindings (publicInputs type)) (result.encode body) = some expression ∧
          func = scalarFunc name exportName arity expression) ∨
        (result = .word ∧ ∃ plan, extractScalarRangeWith
          (publicBindings (publicInputs type)) arity body = some plan ∧
          func = plan.func name exportName arity) ∨
        (result = .word ∧ ∃ plan, extractScalarRangeExitWith
          (publicBindings (publicInputs type)) arity body = some plan ∧
          func = plan.func name exportName arity) ∨
        (result = .boolean ∧ ∃ plan, extractScalarBooleanRangeWith
          (publicBindings (publicInputs type)) arity body = some plan ∧
          func = plan.func name exportName arity) ∨
        (result = .word ∧ ∃ plan, extractScalarWordRangeWith
          (publicBindings (publicInputs type)) arity body = some plan ∧
          func = plan.func name exportName arity) ∨
        (result = .word ∧ ∃ plan, extractScalarSequenceWith
          (publicBindings (publicInputs type)) arity body = some plan ∧
          func = plan.func name exportName arity) ∨
        (result = .boolean ∧ ∃ plan, extractScalarBooleanSequenceWith
          (publicBindings (publicInputs type)) arity body = some plan ∧
          func = plan.func name exportName arity)) := by
  unfold extractScalarFunc at compiled
  simp only [bind, Option.bind_eq_some_iff] at compiled
  obtain ⟨⟨arity, result⟩, ha, compiled⟩ := compiled
  cases annotations : publicLambdasMatch (publicInputs type) source with
  | false => simp [annotations] at compiled
  | true =>
    simp only [annotations, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Option.bind_eq_some_iff] at compiled
    obtain ⟨body, hb, compiled⟩ := compiled
    refine ⟨arity, result, body, ha, rfl, hb, ?_⟩
    cases pureCase : extractScalarExprWith (publicBindings (publicInputs type)) (result.encode body) with
    | some expression =>
      simp only [pureCase, pure, Option.some.injEq] at compiled
      exact .inl ⟨expression, rfl, compiled.symm⟩
    | none =>
      simp only [pureCase] at compiled
      cases result with
      | boolean =>
        cases prior : extractScalarBooleanRangeWith (publicBindings (publicInputs type)) arity body with
        | some plan =>
          simp only [prior, pure, Option.some.injEq] at compiled
          exact .inr (.inr (.inr (.inl ⟨rfl, plan, rfl, compiled.symm⟩)))
        | none =>
          simp only [prior, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
          obtain ⟨plan, hp, same⟩ := compiled
          exact .inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, plan, hp, same.symm⟩)))))
      | word =>
        cases rangeCase : extractScalarRangeWith
            (publicBindings (publicInputs type)) arity body with
        | some plan =>
          simp only [rangeCase, pure, Option.some.injEq] at compiled
          exact .inr (.inl ⟨rfl, plan, rfl, compiled.symm⟩)
        | none =>
          simp only [rangeCase] at compiled
          cases exitCase : extractScalarRangeExitWith (publicBindings (publicInputs type)) arity body with
          | some plan =>
            simp only [exitCase, pure, Option.some.injEq] at compiled
            exact .inr (.inr (.inl ⟨rfl, plan, rfl, compiled.symm⟩))
          | none =>
            simp only [exitCase] at compiled
            cases wordCase : extractScalarWordRangeWith (publicBindings (publicInputs type)) arity body with
            | some plan =>
              simp only [wordCase, pure, Option.some.injEq] at compiled
              exact .inr (.inr (.inr (.inr (.inl ⟨rfl, plan, rfl, compiled.symm⟩))))
            | none =>
              simp only [wordCase, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
              obtain ⟨plan, hp, same⟩ := compiled
              exact .inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, plan, hp, same.symm⟩)))))

theorem extractScalarFunc_properties {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name exportName type source = some func) :
    func.exportName = exportName ∧ func.params ≤ func.locals ∧ func.results = [.local func.params] := by
  obtain ⟨arity, result, body, _, _, _, cases⟩ := extractScalarFunc_cases compiled
  rcases cases with ⟨expression, _, rfl⟩ | ⟨rfl, plan, _, rfl⟩ | ⟨rfl, plan, _, rfl⟩ | ⟨rfl, plan, _, rfl⟩ | ⟨rfl, plan, _, rfl⟩ | ⟨rfl, plan, _, rfl⟩ | ⟨rfl, plan, _, rfl⟩
  · simp [scalarFunc]
  · simp [ScalarRangePlan.func]
  · simp [ScalarRangeExitPlan.func]
  · simp [ScalarRangeExitPlan.func]
  · simp [ScalarRangeExitPlan.func]

  · simp [ScalarSequencePlan.func]

  · simp [ScalarSequencePlan.func]


theorem scalarArgumentLocals (args scratch : List UInt64) :
    ScalarLocalsMatch (List.range args.length).reverse args.reverse (args ++ scratch) := by
  intro index slot hslot
  have hi : index < args.length := by
    have := (List.getElem?_eq_some_iff.mp hslot).1
    simpa using this
  have hj : args.length - 1 - index < args.length := by omega
  rw [List.getElem?_reverse (by simpa using hi)] at hslot
  simp only [List.length_range] at hslot
  rw [List.getElem?_range hj] at hslot
  cases hslot
  rw [List.getElem?_append_left hj, List.getElem?_reverse hi]

theorem scalarFunc_of_eval {arity : Nat} {expression : LeanExe.IR.Expr}
    {args : List UInt64} (len : args.length = arity) {value : UInt64}
    (heval : expression.ScalarEval (args ++ [0]) value (args ++ [0]))
    (name : Lean.Name) (exportName : Option String) :
    (scalarFunc name exportName arity expression).ScalarEval args value := by
  subst arity
  have hwrite : LeanExe.IR.ScalarStore.write (args ++ [0]) args.length value =
      some ((args ++ [0]).set args.length value) := by
    simp [LeanExe.IR.ScalarStore.write]
  refine .run (afterBody := (args ++ [0]).set args.length value)
    (afterResult := (args ++ [0]).set args.length value) rfl (by simp [scalarFunc]) ?_ rfl ?_
  · simpa [scalarFunc] using LeanExe.IR.Stmt.ScalarEval.assign heval hwrite
  · exact .local (LeanExe.IR.ScalarStore.read_write_same hwrite)

theorem scalarFunc_correct {body : Lean.Expr} {arity : Nat} {expression : LeanExe.IR.Expr}
    (compiled : extractScalarExpr (List.range arity).reverse body = some expression)
    {args : List UInt64} (len : args.length = arity) {value : UInt64}
    (semantics : LeanExe.Source.Scalar.Eval body args.reverse value)
    (name : Lean.Name) (exportName : Option String) :
    (scalarFunc name exportName arity expression).ScalarEval args value := by
  subst arity
  exact scalarFunc_of_eval rfl
    (extractScalarExpr_correct semantics compiled (scalarArgumentLocals args [0])) name exportName

/-- Every public argument binding matches its typed, decoded source value. -/
theorem publicArgumentBindings (inputs : List PublicArgument) (args scratch : List UInt64)
    (len : args.length = inputs.length) :
    ScalarBindingsMatch (publicBindings inputs) (publicValues inputs args).reverse (args ++ scratch) := by
  unfold publicBindings
  have reversed : (publicValues inputs args).reverse = publicValues inputs.reverse args.reverse := by
    exact List.reverse_zipWith len.symm
  rw [reversed, ← len]
  apply publicBindingsFor_matches
  intro index slot value hs hv
  exact (scalarArgumentLocals args scratch index slot hs).trans hv

/-- Typed source evaluation and the corresponding IR evaluation for public inputs. -/
theorem scalarPublic_meaning {body : Lean.Expr} {inputs : List PublicArgument}
    {expression : LeanExe.IR.Expr}
    (compiled : extractScalarExprWith (publicBindings inputs) body = some expression)
    (args scratch : List UInt64) (len : args.length = inputs.length) :
    ∃ value, LeanExe.Source.Scalar.EvalWith body (publicValues inputs args).reverse value ∧
      expression.ScalarEval (args ++ scratch) value (args ++ scratch) := by
  have supported := extractScalarExprWith_supported compiled
  obtain ⟨value, semantics⟩ := supported.evaluates (publicValues inputs args).reverse (publicValues_bindings_typed len)
  exact ⟨value, semantics,
    extractScalarExprWith_correct semantics compiled (publicArgumentBindings inputs args scratch len)⟩

/-- Apply the original typed lambdas and evaluate their compiled scalar expression. -/
theorem scalarPublic_application {type source body : Lean.Expr} {arity : Nat}
    {result : LeanExe.Source.Scalar.PublicResult} {expression : LeanExe.IR.Expr}
    (signature : scalarSignature? type = some (arity, result))
    (annotations : publicLambdasMatch (publicInputs type) source = true)
    (lambdas : collectLambdas source arity = some body)
    (compiled : extractScalarExprWith (publicBindings (publicInputs type)) (result.encode body) = some expression)
    (args scratch : List UInt64) (len : args.length = arity) :
    ∃ value, LeanExe.Source.Scalar.Apply source [] args value ∧
      expression.ScalarEval (args ++ scratch) value (args ++ scratch) := by
  have inputLen : args.length = (publicInputs type).length :=
    len.trans (scalarSignature_inputs_length signature).symm
  obtain ⟨value, semantics, evaluated⟩ := scalarPublic_meaning compiled args scratch inputLen
  exact ⟨value, LeanExe.Source.Scalar.apply_typed_of_collectLambdas result (publicInputs type)
    args [] inputLen annotations (by simpa [len] using lambdas) (by simpa using semantics), evaluated⟩

theorem extractScalarFunc_accepts {type value : Lean.Expr}
    (supported : LeanExe.Source.Scalar.DeclarationSupported type value)
    (name : Lean.Name) (exportName : Option String) :
    ∃ func, extractScalarFunc name exportName type value = some func := by
  obtain ⟨arity, result, body, signature, annotations, lambdas, supportedBody⟩ := supported
  rcases supportedBody with supportedBody | ⟨rfl, supportedBody | supportedBody⟩ | ⟨rfl, supportedBody⟩ | ⟨rfl, supportedBody⟩ | ⟨rfl, supportedBody⟩ | ⟨rfl, supportedBody⟩
  ·
    obtain ⟨expression, compiled⟩ := extractScalarExprWith_accepts supportedBody
      (publicBindings (publicInputs type)) (publicBindings_typed _) (publicBindings_total _)
    exact ⟨scalarFunc name exportName arity expression,
      by simp [extractScalarFunc, scalarSignature_accepts signature, annotations, Bool.not_true, Bool.false_eq_true, ↓reduceIte, lambdas, compiled]⟩
  ·
    let locals := publicBindings (publicInputs type)
    obtain ⟨plan, compiled⟩ := extractScalarRangeWith_accepts supportedBody locals arity
      (publicBindings_typed _) (publicBindings_total _)
    have excluded := rangeSupported_excludes_pure supportedBody locals
    exact ⟨plan.func name exportName arity, by
      simp only [extractScalarFunc, scalarSignature_accepts signature, annotations, Bool.not_true, Bool.false_eq_true, ↓reduceIte, lambdas, bind, Option.bind, LeanExe.Source.Scalar.PublicResult.encode]
      rw [excluded]
      rw [compiled]
      rfl⟩
  · let locals := publicBindings (publicInputs type)
    obtain ⟨plan, compiled⟩ := extractScalarRangeExitWith_accepts supportedBody locals arity
      (publicBindings_typed _) (publicBindings_total _)
    have excluded := rangeExitSupported_excludes_pure supportedBody locals
    cases rangeCase : extractScalarRangeWith locals arity body with
    | some yielding =>
      exact ⟨yielding.func name exportName arity, by
        simp only [extractScalarFunc, scalarSignature_accepts signature, annotations, Bool.not_true, Bool.false_eq_true, ↓reduceIte, lambdas, bind, Option.bind, LeanExe.Source.Scalar.PublicResult.encode]
        rw [excluded, rangeCase]
        rfl⟩
    | none =>
      exact ⟨plan.func name exportName arity, by
        simp only [extractScalarFunc, scalarSignature_accepts signature, annotations, Bool.not_true, Bool.false_eq_true, ↓reduceIte, lambdas, bind, Option.bind, LeanExe.Source.Scalar.PublicResult.encode]
        rw [excluded, rangeCase, compiled]
        rfl⟩
  · let locals := publicBindings (publicInputs type)
    obtain ⟨plan, compiled⟩ := extractScalarBooleanRangeWith_accepts supportedBody locals arity
      (publicBindings_typed _) (publicBindings_total _)
    cases pureCase : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) body) with
    | some expression =>
      exact ⟨scalarFunc name exportName arity expression, by
        simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
          LeanExe.Source.Scalar.PublicResult.encode, pureCase, locals] at *⟩
    | none =>
      exact ⟨plan.func name exportName arity, by
        simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
          LeanExe.Source.Scalar.PublicResult.encode, pureCase, compiled, locals] at *⟩

  · let locals := publicBindings (publicInputs type)
    obtain ⟨plan, compiled⟩ := extractScalarWordRangeWith_accepts supportedBody locals arity
      (publicBindings_typed _) (publicBindings_total _)
    cases pureCase : extractScalarExprWith locals body with
    | some expression =>
      exact ⟨scalarFunc name exportName arity expression, by
        simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
          LeanExe.Source.Scalar.PublicResult.encode, pureCase, locals] at *⟩
    | none =>
      cases rangeCase : extractScalarRangeWith locals arity body with
      | some prior =>
        exact ⟨prior.func name exportName arity, by
          simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
            LeanExe.Source.Scalar.PublicResult.encode, pureCase, rangeCase, locals] at *⟩
      | none =>
        cases exitCase : extractScalarRangeExitWith locals arity body with
        | some prior =>
          exact ⟨prior.func name exportName arity, by
            simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
              LeanExe.Source.Scalar.PublicResult.encode, pureCase, rangeCase, exitCase, locals] at *⟩
        | none =>
          exact ⟨plan.func name exportName arity, by
            simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
              LeanExe.Source.Scalar.PublicResult.encode, pureCase, rangeCase, exitCase, compiled, locals] at *⟩
  · let locals := publicBindings (publicInputs type)
    obtain ⟨plan, compiled⟩ := extractScalarSequenceWith_accepts supportedBody locals arity
      (publicBindings_typed _) (publicBindings_total _)
    cases pureCase : extractScalarExprWith locals body with
    | some expression =>
      exact ⟨scalarFunc name exportName arity expression, by
        simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
          LeanExe.Source.Scalar.PublicResult.encode, pureCase, locals] at *⟩
    | none =>
      cases rangeCase : extractScalarRangeWith locals arity body with
      | some prior =>
        exact ⟨prior.func name exportName arity, by
          simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
            LeanExe.Source.Scalar.PublicResult.encode, pureCase, rangeCase, locals] at *⟩
      | none =>
        cases exitCase : extractScalarRangeExitWith locals arity body with
        | some prior =>
          exact ⟨prior.func name exportName arity, by
            simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
              LeanExe.Source.Scalar.PublicResult.encode, pureCase, rangeCase, exitCase, locals] at *⟩
        | none =>
          cases wordCase : extractScalarWordRangeWith locals arity body with
          | some prior =>
            exact ⟨prior.func name exportName arity, by
              simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
                LeanExe.Source.Scalar.PublicResult.encode, pureCase, rangeCase, exitCase, wordCase, locals] at *⟩
          | none =>
            exact ⟨plan.func name exportName arity, by
              simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
                LeanExe.Source.Scalar.PublicResult.encode, pureCase, rangeCase, exitCase, wordCase, compiled, locals] at *⟩
  · let locals := publicBindings (publicInputs type)
    obtain ⟨plan, compiled⟩ := extractScalarBooleanSequenceWith_accepts supportedBody locals arity
      (publicBindings_typed _) (publicBindings_total _)
    cases pureCase : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) body) with
    | some expression =>
      exact ⟨scalarFunc name exportName arity expression, by
        simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
          LeanExe.Source.Scalar.PublicResult.encode, pureCase, locals] at *⟩
    | none =>
      cases prior : extractScalarBooleanRangeWith locals arity body with
      | some original =>
        exact ⟨original.func name exportName arity, by
          simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
            LeanExe.Source.Scalar.PublicResult.encode, pureCase, prior, locals] at *⟩
      | none =>
        exact ⟨plan.func name exportName arity, by
          simp [extractScalarFunc, scalarSignature_accepts signature, annotations, lambdas,
            LeanExe.Source.Scalar.PublicResult.encode, pureCase, prior, compiled, locals] at *⟩

/-- Actual argument locals match the source environment for any trailing locals. -/
theorem scalarArgumentBindings (args extra : List UInt64) :
    ScalarBindingsMatch ((List.range args.length).reverse.map fun slot => .word (.local slot))
      (args.reverse.map LeanExe.Source.Scalar.Value.word) (args ++ extra) := by
  intro index binding value he hv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at he hv
  obtain ⟨slot, hs, rfl⟩ := he
  obtain ⟨word, hw, rfl⟩ := hv
  exact LeanExe.IR.Expr.ScalarEval.local ((scalarArgumentLocals args extra _ _ hs).trans hw)

/-- Source value and loop facts for a successfully extracted range function. -/
theorem rangeFunc_meaning {body : Lean.Expr} {arity : Nat} {plan : ScalarRangePlan}
    (compiled : extractScalarRangeWith
      ((List.range arity).reverse.map fun slot => .word (.local slot)) arity body = some plan)
    {args : List UInt64} (len : args.length = arity) :
    ∃ value, LeanExe.Source.Scalar.Eval body args.reverse value ∧ plan.Meaning args value := by
  subst arity
  apply extractScalarRangeWith_correct args (args.reverse.map LeanExe.Source.Scalar.Value.word) compiled
  · simp [List.map_map, Function.comp_def, LeanExe.Source.Scalar.Value.kind, ScalarBinding.kind, List.map_const']
  · intro accumulator index stop
    exact scalarArgumentBindings args [accumulator, UInt64.ofNat index, stop]
  · intro binding member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    trivial

/-- Source value and iteration facts for a successfully extracted early-exit range. -/
theorem rangeExitFunc_meaning {body : Lean.Expr} {arity : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarRangeExitWith
      ((List.range arity).reverse.map fun slot => .word (.local slot)) arity body = some plan)
    {args : List UInt64} (len : args.length = arity) :
    ∃ value, LeanExe.Source.Scalar.Range.Exit.Eval body
      (args.reverse.map LeanExe.Source.Scalar.Value.word) value ∧ plan.Meaning args value := by
  subst arity
  apply extractScalarRangeExitWith_correct args (args.reverse.map LeanExe.Source.Scalar.Value.word) compiled
  · simp [List.map_map, Function.comp_def, LeanExe.Source.Scalar.Value.kind, ScalarBinding.kind, List.map_const']
  · intro accumulator index stop flag
    exact scalarArgumentBindings args [accumulator, UInt64.ofNat index, stop, flag]
  · intro binding member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    trivial

/-- Typed captured public arguments retain their values throughout the loop. -/
theorem rangePublic_application {type source body : Lean.Expr} {arity : Nat}
    {plan : ScalarRangePlan}
    (signature : scalarSignature? type = some (arity, .word))
    (annotations : publicLambdasMatch (publicInputs type) source = true)
    (lambdas : collectLambdas source arity = some body)
    (compiled : extractScalarRangeWith (publicBindings (publicInputs type)) arity body = some plan)
    (args : List UInt64) (len : args.length = arity) :
    ∃ value, LeanExe.Source.Scalar.Apply source [] args value ∧ plan.Meaning args value := by
  subst arity
  have inputLen := (scalarSignature_inputs_length signature).symm
  have meaning : ∃ value, LeanExe.Source.Scalar.EvalWith body
      (publicValues (publicInputs type) args).reverse value ∧ plan.Meaning args value := by
    apply extractScalarRangeWith_correct args (publicValues (publicInputs type) args).reverse compiled
    · exact publicValues_bindings_typed inputLen
    · intro accumulator index stop
      exact publicArgumentBindings (publicInputs type) args [accumulator, UInt64.ofNat index, stop] inputLen
    · exact publicBindings_total _
  obtain ⟨value, semantics, meaning⟩ := meaning
  refine ⟨value, ?_, meaning⟩
  apply LeanExe.Source.Scalar.apply_of_publicLambdas (publicInputs type) args [] inputLen annotations lambdas
  apply LeanExe.Source.Scalar.Apply.done
  simpa using semantics

/-- Typed captured public arguments retain their values throughout the loop. -/
theorem rangeExitPublic_application {type source body : Lean.Expr} {arity : Nat}
    {plan : ScalarRangeExitPlan}
    (signature : scalarSignature? type = some (arity, .word))
    (annotations : publicLambdasMatch (publicInputs type) source = true)
    (lambdas : collectLambdas source arity = some body)
    (compiled : extractScalarRangeExitWith (publicBindings (publicInputs type)) arity body = some plan)
    (args : List UInt64) (len : args.length = arity) :
    ∃ value, LeanExe.Source.Scalar.Apply source [] args value ∧ plan.Meaning args value := by
  subst arity
  have inputLen := (scalarSignature_inputs_length signature).symm
  have meaning : ∃ value, LeanExe.Source.Scalar.Range.Exit.Eval body
      (publicValues (publicInputs type) args).reverse value ∧ plan.Meaning args value := by
    apply extractScalarRangeExitWith_correct args (publicValues (publicInputs type) args).reverse compiled
    · exact publicValues_bindings_typed inputLen
    · intro accumulator index stop flag
      exact publicArgumentBindings (publicInputs type) args [accumulator, UInt64.ofNat index, stop, flag] inputLen
    · exact publicBindings_total _
  obtain ⟨value, semantics, meaning⟩ := meaning
  refine ⟨value, ?_, meaning⟩
  apply LeanExe.Source.Scalar.apply_of_publicLambdas (publicInputs type) args [] inputLen annotations lambdas
  apply LeanExe.Source.Scalar.Apply.exit
  simpa using semantics

/-- A public Boolean continuation preserves the original term and its loop result. -/
theorem booleanRangePublic_application {type source body : Lean.Expr} {arity : Nat}
    {plan : ScalarRangeExitPlan}
    (signature : scalarSignature? type = some (arity, .boolean))
    (annotations : publicLambdasMatch (publicInputs type) source = true)
    (lambdas : collectLambdas source arity = some body)
    (compiled : extractScalarBooleanRangeWith (publicBindings (publicInputs type)) arity body = some plan)
    (args : List UInt64) (len : args.length = arity) :
    ∃ flag : Bool, LeanExe.Source.Scalar.Apply source [] args flag.toUInt64 ∧ plan.Meaning args flag.toUInt64 := by
  subst arity
  have inputLen := (scalarSignature_inputs_length signature).symm
  obtain ⟨flag, evaluated, meaning⟩ := extractScalarBooleanRangeWith_correct args
    (publicValues (publicInputs type) args).reverse compiled (publicValues_bindings_typed inputLen)
    (fun accumulator index stop flag =>
      publicArgumentBindings (publicInputs type) args [accumulator, UInt64.ofNat index, stop, flag] inputLen)
    (publicBindings_total _)
  refine ⟨flag, ?_, meaning⟩
  apply LeanExe.Source.Scalar.apply_of_publicLambdas (publicInputs type) args [] inputLen annotations lambdas
  apply LeanExe.Source.Scalar.Apply.booleanRangeDone
  simpa using evaluated

/-- A public word continuation uses the native result of its Boolean loop. -/
theorem wordRangePublic_application {type source body : Lean.Expr} {arity : Nat}
    {plan : ScalarRangeExitPlan}
    (signature : scalarSignature? type = some (arity, .word))
    (annotations : publicLambdasMatch (publicInputs type) source = true)
    (lambdas : collectLambdas source arity = some body)
    (compiled : extractScalarWordRangeWith (publicBindings (publicInputs type)) arity body = some plan)
    (args : List UInt64) (len : args.length = arity) :
    ∃ value, LeanExe.Source.Scalar.Apply source [] args value ∧ plan.Meaning args value := by
  subst arity
  have inputLen := (scalarSignature_inputs_length signature).symm
  obtain ⟨value, evaluated, meaning⟩ := extractScalarWordRangeWith_correct args
    (publicValues (publicInputs type) args).reverse compiled (publicValues_bindings_typed inputLen)
    (fun accumulator index stop flag =>
      publicArgumentBindings (publicInputs type) args [accumulator, UInt64.ofNat index, stop, flag] inputLen)
    (publicBindings_total _)
  refine ⟨value, ?_, meaning⟩
  apply LeanExe.Source.Scalar.apply_of_publicLambdas (publicInputs type) args [] inputLen annotations lambdas
  apply LeanExe.Source.Scalar.Apply.wordRangeDone
  simpa using evaluated

/-- Public word arguments and every prior loop result retain their native values. -/
theorem sequencePublic_application {type source body : Lean.Expr} {arity : Nat}
    {plan : ScalarSequencePlan}
    (signature : scalarSignature? type = some (arity, .word))
    (annotations : publicLambdasMatch (publicInputs type) source = true)
    (lambdas : collectLambdas source arity = some body)
    (compiled : extractScalarSequenceWith (publicBindings (publicInputs type)) arity body = some plan)
    (args : List UInt64) (len : args.length = arity) :
    ∃ value, LeanExe.Source.Scalar.Apply source [] args value ∧ plan.Meaning args value := by
  subst arity
  have inputLen := (scalarSignature_inputs_length signature).symm
  obtain ⟨value, evaluated, meaning⟩ := extractScalarSequenceWith_correct compiled args
    (publicValues (publicInputs type) args).reverse rfl (publicValues_bindings_typed inputLen)
    (fun suffix => publicArgumentBindings (publicInputs type) args suffix inputLen)
    (publicBindings_total _)
  refine ⟨value, ?_, meaning⟩
  apply LeanExe.Source.Scalar.apply_of_publicLambdas (publicInputs type) args [] inputLen annotations lambdas
  apply LeanExe.Source.Scalar.Apply.sequenceDone
  simpa using evaluated

/-- A Boolean sequence preserves prior word results and returns an encoded native flag. -/
theorem booleanSequencePublic_application {type source body : Lean.Expr} {arity : Nat}
    {plan : ScalarSequencePlan}
    (signature : scalarSignature? type = some (arity, .boolean))
    (annotations : publicLambdasMatch (publicInputs type) source = true)
    (lambdas : collectLambdas source arity = some body)
    (compiled : extractScalarBooleanSequenceWith (publicBindings (publicInputs type)) arity body = some plan)
    (args : List UInt64) (len : args.length = arity) :
    ∃ value : Bool, LeanExe.Source.Scalar.Apply source [] args value.toUInt64 ∧ plan.Meaning args value.toUInt64 := by
  subst arity
  have inputLen := (scalarSignature_inputs_length signature).symm
  obtain ⟨value, evaluated, meaning⟩ := extractScalarBooleanSequenceWith_correct compiled args
    (publicValues (publicInputs type) args).reverse rfl (publicValues_bindings_typed inputLen)
    (fun suffix => publicArgumentBindings (publicInputs type) args suffix inputLen)
    (publicBindings_total _)
  refine ⟨value, ?_, meaning⟩
  apply LeanExe.Source.Scalar.apply_of_publicLambdas (publicInputs type) args [] inputLen annotations lambdas
  apply LeanExe.Source.Scalar.Apply.booleanSequenceDone
  simpa using evaluated

/-- Every successful scalar declaration extraction preserves application of
the original source term on every argument list of the declared arity. -/
theorem extractScalarFunc_correct {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name exportName type source = some func)
    (args : List UInt64) (len : args.length = func.params) :
    ∃ value, LeanExe.Source.Scalar.Apply source [] args value ∧ func.ScalarEval args value := by
  obtain ⟨arity, result, body, signature, annotations, hb, cases⟩ := extractScalarFunc_cases compiled
  rcases cases with ⟨expression, he, rfl⟩ | ⟨rfl, plan, hp, rfl⟩ | ⟨rfl, plan, hp, rfl⟩ | ⟨rfl, plan, hp, rfl⟩ | ⟨rfl, plan, hp, rfl⟩ | ⟨rfl, plan, hp, rfl⟩ | ⟨rfl, plan, hp, rfl⟩
  · have hlen : args.length = arity := len
    obtain ⟨value, applied, evaluated⟩ := scalarPublic_application signature annotations hb he args [0] hlen
    exact ⟨value, applied, scalarFunc_of_eval hlen evaluated name exportName⟩
  · have hlen : args.length = arity := len
    obtain ⟨value, applied, meaning⟩ := rangePublic_application signature annotations hb hp args hlen
    exact ⟨value, applied, by simpa [hlen] using meaning.func_correct name exportName⟩
  · have hlen : args.length = arity := len
    obtain ⟨value, applied, meaning⟩ := rangeExitPublic_application signature annotations hb hp args hlen
    exact ⟨value, applied, by simpa [hlen] using meaning.func_correct name exportName⟩
  · have hlen : args.length = arity := len
    obtain ⟨flag, applied, meaning⟩ := booleanRangePublic_application signature annotations hb hp args hlen
    exact ⟨flag.toUInt64, applied, by simpa [hlen] using meaning.func_correct name exportName⟩

  · have hlen : args.length = arity := len
    obtain ⟨value, applied, meaning⟩ := wordRangePublic_application signature annotations hb hp args hlen
    exact ⟨value, applied, by simpa [hlen] using meaning.func_correct name exportName⟩

  · have hlen : args.length = arity := len
    obtain ⟨value, applied, meaning⟩ := sequencePublic_application signature annotations hb hp args hlen
    exact ⟨value, applied, by simpa [hlen] using meaning.func_correct name exportName⟩

  · have hlen : args.length = arity := len
    obtain ⟨flag, applied, meaning⟩ := booleanSequencePublic_application signature annotations hb hp args hlen
    exact ⟨flag.toUInt64, applied, by simpa [hlen] using meaning.func_correct name exportName⟩

/-- A public Bool result uses either a scalar conversion or a checked loop continuation. -/
theorem extractScalarFunc_boolean_cases {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func} {arity : Nat}
    (compiled : extractScalarFunc name exportName type source = some func)
    (signature : scalarSignature? type = some (arity, .boolean)) :
    ∃ body, publicLambdasMatch (publicInputs type) source = true ∧
      collectLambdas source arity = some body ∧
      ((∃ expression, extractScalarExprWith (publicBindings (publicInputs type))
          (.app (.const ``Bool.toUInt64 []) body) = some expression ∧
          func = scalarFunc name exportName arity expression) ∨
        (∃ plan, extractScalarBooleanRangeWith (publicBindings (publicInputs type)) arity body = some plan ∧
          func = plan.func name exportName arity) ∨
        (∃ plan, extractScalarBooleanSequenceWith (publicBindings (publicInputs type)) arity body = some plan ∧
          func = plan.func name exportName arity)) := by
  obtain ⟨foundArity, result, body, parsed, annotations, lambdas, branches⟩ := extractScalarFunc_cases compiled
  have same := Option.some.inj (parsed.symm.trans signature)
  cases same
  refine ⟨body, annotations, lambdas, ?_⟩
  rcases branches with ⟨expression, extracted, same⟩ | ⟨impossible, _⟩ | ⟨impossible, _⟩ | ⟨_, plan, extracted, same⟩ | ⟨impossible, _⟩ | ⟨impossible, _⟩ | ⟨_, plan, extracted, same⟩
  · exact .inl ⟨expression, extracted, same⟩
  · cases impossible
  · cases impossible
  · exact .inr (.inl ⟨plan, extracted, same⟩)
  · cases impossible
  · cases impossible
  · exact .inr (.inr ⟨plan, extracted, same⟩)

/-- Every admitted public Bool function returns the native flag encoded as zero
or one, for every argument list of the declared arity. -/
theorem extractScalarFunc_boolean_correct {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func} {arity : Nat}
    (compiled : extractScalarFunc name exportName type source = some func)
    (signature : scalarSignature? type = some (arity, .boolean))
    (args : List UInt64) (len : args.length = arity) :
    ∃ flag : Bool, LeanExe.Source.Scalar.Apply source [] args flag.toUInt64 ∧
      func.ScalarEval args flag.toUInt64 := by
  obtain ⟨body, annotations, lambdas, branches⟩ := extractScalarFunc_boolean_cases compiled signature
  rcases branches with ⟨expression, extracted, rfl⟩ | ⟨plan, extracted, rfl⟩ | ⟨plan, extracted, rfl⟩
  ·
    have inputLen : args.length = (publicInputs type).length :=
      len.trans (scalarSignature_inputs_length signature).symm
    obtain ⟨value, semantics, evaluated⟩ := scalarPublic_meaning extracted args [0] inputLen
    obtain ⟨flag, rfl⟩ := semantics.booleanConversion_result
    refine ⟨flag, ?_, scalarFunc_of_eval len evaluated name exportName⟩
    exact LeanExe.Source.Scalar.apply_typed_of_collectLambdas .boolean (publicInputs type)
      args [] inputLen annotations (by simpa [len] using lambdas)
      (by simpa [LeanExe.Source.Scalar.PublicResult.encode] using semantics)
  · obtain ⟨flag, applied, meaning⟩ := booleanRangePublic_application signature annotations lambdas extracted args len
    exact ⟨flag, applied, by simpa [len] using meaning.func_correct name exportName⟩
  · obtain ⟨flag, applied, meaning⟩ := booleanSequencePublic_application signature annotations lambdas extracted args len
    exact ⟨flag, applied, by simpa [len] using meaning.func_correct name exportName⟩

end LeanExe.Extract.Core
