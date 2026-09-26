import LeanExe.Extract.ScalarStepEquations

namespace LeanExe.Extract.Core

/-- Both emitted projections describe the same source step, including across
captured continuations. Their evaluation preserves all source locals. -/
theorem extractScalarStepWith_correct {source : Lean.Expr}
    {values : List LeanExe.Source.Scalar.Step.Value} {outcome : ForInStep UInt64}
    (semantics : LeanExe.Source.Scalar.Step.Eval source values outcome)
    {locals : List ScalarStepBinding} {code : ScalarStepCode} {store : LeanExe.IR.ScalarStore}
    (compiled : extractScalarStepWith locals source = some code)
    (bindings : ScalarStepBindingsMatch locals values store) : code.Meaning store outcome := by
  induction semantics generalizing locals code with
  | yieldValue value =>
    rw [extractScalarStepWith_yield] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨target, ht, rfl⟩ := compiled
    exact ⟨extractScalarExprWith_correct value ht bindings.toScalar, .const⟩
  | doneValue value =>
    rw [extractScalarStepWith_done] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨target, ht, rfl⟩ := compiled
    exact ⟨extractScalarExprWith_correct value ht bindings.toScalar, .const⟩
  | yieldDirect value =>
    rw [extractScalarStepWith_yieldDirect] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨target, ht, rfl⟩ := compiled
    exact ⟨extractScalarExprWith_correct value ht bindings.toScalar, .const⟩
  | doneDirect value =>
    rw [extractScalarStepWith_doneDirect] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨target, ht, rfl⟩ := compiled
    exact ⟨extractScalarExprWith_correct value ht bindings.toScalar, .const⟩
  | @choose a x b y t e values outcome op type left right chosen ih =>
    rw [extractScalarStepWith_branch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨ai, ha, bi, hb, ti, ht, ei, he, rfl⟩ := compiled
    have condition := lowerComparison_correct op
      (extractScalarExprWith_correct left ha bindings.toScalar)
      (extractScalarExprWith_correct right hb bindings.toScalar)
    cases flag : op.denote x y with
    | false =>
      obtain ⟨valueEval, doneEval⟩ := ih (by simpa [flag] using he) bindings
      exact ⟨.iteFalse (by simpa [flag] using condition) valueEval,
        .iteFalse (by simpa [flag] using condition) doneEval⟩
    | true =>
      obtain ⟨valueEval, doneEval⟩ := ih (by simpa [flag] using ht) bindings
      exact ⟨.iteTrue (by simpa [flag] using condition) valueEval,
        .iteTrue (by simpa [flag] using condition) doneEval⟩
  | @chooseCompound values t e outcome guard type native arguments _ ih =>
    rw [extractScalarStepWith_compoundBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, rfl⟩ := compiled
    have condition := extractGuard_correct guard.tree _ native hc
      (fun operand member expression found =>
        extractScalarExprWith_correct (arguments operand member) found bindings.toScalar)
    cases flag : guard.denote native with
    | false =>
      obtain ⟨valueEval, doneEval⟩ := ih (by simpa [flag] using he) bindings
      exact ⟨.iteFalse (by simpa [flag] using condition) valueEval,
        .iteFalse (by simpa [flag] using condition) doneEval⟩
    | true =>
      obtain ⟨valueEval, doneEval⟩ := ih (by simpa [flag] using ht) bindings
      exact ⟨.iteTrue (by simpa [flag] using condition) valueEval,
        .iteTrue (by simpa [flag] using condition) doneEval⟩
  | @chooseDependent values t e outcome guard type tn fn tb fb native arguments _ ih =>
    rw [extractScalarStepWith_dependentBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, rfl⟩ := compiled
    have condition := extractGuard_correct guard _ native hc
      (fun operand member expression found =>
        extractScalarExprWith_correct (arguments operand member) found bindings.toScalar)
    cases flag : guard.denote native with
    | false =>
      obtain ⟨valueEval, doneEval⟩ := ih (by simpa [flag] using he)
        (bindings.cons (binding := .scalar .unit) (value := .scalar .unit) trivial)
      exact ⟨.iteFalse (by simpa [flag] using condition) valueEval,
        .iteFalse (by simpa [flag] using condition) doneEval⟩
    | true =>
      obtain ⟨valueEval, doneEval⟩ := ih (by simpa [flag] using ht)
        (bindings.cons (binding := .scalar .unit) (value := .scalar .unit) trivial)
      exact ⟨.iteTrue (by simpa [flag] using condition) valueEval,
        .iteTrue (by simpa [flag] using condition) doneEval⟩
  | @chooseBooleanDependent values t e outcome guard type tn fn tb fb native booleans variables arguments _ ih =>
    rw [extractScalarStepWith_booleanDependentBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, rfl⟩ := compiled
    have condition := extractBooleanLocalWith_correct guard.value _ native booleans hc bindings.toScalar variables
      (fun operand member expression found =>
        extractScalarExprWith_correct (arguments operand member) found bindings.toScalar)
    cases flag : guard.value.denote native booleans with
    | false =>
      obtain ⟨valueEval, doneEval⟩ := ih (by simpa [flag] using he)
        (bindings.cons (binding := .scalar .unit) (value := .scalar .unit) trivial)
      exact ⟨.iteFalse (by simpa [flag] using condition) valueEval,
        .iteFalse (by simpa [flag] using condition) doneEval⟩
    | true =>
      obtain ⟨valueEval, doneEval⟩ := ih (by simpa [flag] using ht)
        (bindings.cons (binding := .scalar .unit) (value := .scalar .unit) trivial)
      exact ⟨.iteTrue (by simpa [flag] using condition) valueEval,
        .iteTrue (by simpa [flag] using condition) doneEval⟩
  | letBoolean bound _ ihb =>
    rw [extractScalarStepWith_letBoolean] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨value, hv, ht⟩ := compiled
    exact ihb ht (bindings.cons (binding := .scalar (.boolean value))
      (value := .scalar (.boolean _)) (extractScalarExprWith_correct bound hv bindings.toScalar))
  | @idBindBoolean values b value name bi action type native booleans variables arguments body ihb =>
    rw [extractScalarStepWith_booleanBind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    have meaning := extractBooleanLocalWith_correct action.leaf _ native booleans hc bindings.toScalar variables
      (fun operand member target found => extractScalarExprWith_correct (arguments operand member) found bindings.toScalar)
    exact ihb ht (bindings.cons (binding := .scalar (.boolean (guardWord c)))
      (value := .scalar (.boolean _)) (guardWord_correct meaning))
  | @chooseBoolean values t e value guard type native booleans variables arguments branch ihb =>
    rw [extractScalarStepWith_booleanBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, rfl⟩ := compiled
    have condition := extractBooleanLocalWith_correct guard.value _ native booleans hc bindings.toScalar variables
      (fun operand member expression found => extractScalarExprWith_correct (arguments operand member) found bindings.toScalar)
    cases flag : guard.value.denote native booleans with
    | false =>
      obtain ⟨v, d⟩ := ihb (by simpa [flag] using he) bindings
      exact ⟨.iteFalse (by simpa [flag] using condition) v, .iteFalse (by simpa [flag] using condition) d⟩
    | true =>
      obtain ⟨v, d⟩ := ihb (by simpa [flag] using ht) bindings
      exact ⟨.iteTrue (by simpa [flag] using condition) v, .iteTrue (by simpa [flag] using condition) d⟩
  | letE value body ih =>
    rw [extractScalarStepWith_letE] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hc⟩ := compiled
    exact ih hc (bindings.cons (extractScalarExprWith_correct value hb bindings.toScalar))
  | idBind type value body ih =>
    rw [extractScalarStepWith_bind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hc⟩ := compiled
    exact ih hc (bindings.cons (extractScalarExprWith_correct value hb bindings.toScalar))
  | letBinaryFn type function body ih =>
    rw [extractScalarStepWith_letBinaryFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ih ht
    apply bindings.cons
    intro first x second y target hx hy hc
    exact extractScalarExprWith_correct (function x y) hc
      ((bindings.toScalar.cons (binding := .word first) (value := .word x) hx).cons
        (binding := .word second) (value := .word y) hy)
  | letManyFn shape function body ih =>
    rw [extractScalarStepWith_letManyFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ih ht
    apply bindings.cons
    intro arguments native target len meanings compiled
    exact extractScalarExprWith_correct (function native (meanings.length.symm.trans len))
      compiled (bindings.toScalar.words meanings.reverse)
  | letFn type function body ih =>
    rw [extractScalarStepWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ih ht
    apply bindings.cons
    intro argument value target ha hc
    exact extractScalarExprWith_correct (function value) hc (bindings.toScalar.cons ha)
  | letPredicateFn expression type variables arguments _ ih =>
    rw [extractScalarStepWith_letPredicateFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ih ht
    apply bindings.cons
    intro argument value target ha compiled
    simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    have inner := bindings.toScalar.cons (binding := .word argument) (value := .word value) ha
    exact guardWord_correct (extractBooleanLocalWith_correct expression _ _ _ hc inner
      (variables value) (fun operand member expression found =>
        extractScalarExprWith_correct (arguments value operand member) found inner))
  | letBooleanPredicateFn expression type variables arguments _ ih =>
    rw [extractScalarStepWith_letBooleanPredicateFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ih ht
    apply bindings.cons
    intro argument value target ha compiled
    simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    have inner := bindings.toScalar.cons (binding := .boolean argument) (value := .boolean value) ha
    exact guardWord_correct (extractBooleanLocalWith_correct expression _ _ _ hc inner
      (variables value) (fun operand member expression found =>
        extractScalarExprWith_correct (arguments value operand member) found inner))
  | predicateInput input result _ ih =>
    rw [extractScalarStepWith_predicateInput] at compiled
    exact ih compiled bindings
  | letBooleanFn type function body ih =>
    rw [extractScalarStepWith_letBooleanFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ih ht
    apply bindings.cons
    intro argument value target ha hc
    exact extractScalarExprWith_correct (function value) hc (bindings.toScalar.cons ha)
  | letUnitFn type unitForm function body ih =>
    rw [extractScalarStepWith_letUnitFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ih ht
    apply bindings.cons
    intro argument value target ha hc
    exact extractScalarExprWith_correct (function value) hc
      ((bindings.toScalar.cons (binding := .unit) (value := .unit) trivial).cons ha)
  | manyApply call function arguments =>
    rw [extractScalarStepWith_manyApply] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, compiledArguments, ha, ht⟩ := compiled
    apply bindings.manyFunction (Option.bind_eq_some_iff.mpr hf) function compiledArguments _ code
      (extractScalarArguments_length _ _ ha) ?_ ht
    exact extractScalarArguments_relation call.arguments _ _ _ ha
      (fun operand member expression found =>
        extractScalarExprWith_correct (arguments operand member) found bindings.toScalar)
  | letManyStepFn shape function _ ihf ihb =>
    rw [extractScalarStepWith_letManyStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro arguments native target len meanings compiled
    exact ihf native (meanings.length.symm.trans len) compiled (bindings.words meanings.reverse)
  | binaryApply function first second =>
    rw [extractScalarStepWith_binaryApply _ _ _ _ first.not_unit] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, a, ha, b, hb, hc⟩ := compiled
    exact bindings.binaryFunction (Option.bind_eq_some_iff.mpr hf) function a _ b _ code
      (extractScalarExprWith_correct first ha bindings.toScalar)
      (extractScalarExprWith_correct second hb bindings.toScalar) hc
  | letBinaryStepFn type function body ihf ihb =>
    rw [extractScalarStepWith_letBinaryStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro first x second y target hx hy hc
    exact ihf x y hc
      ((bindings.cons (binding := .scalar (.word first)) (value := .scalar (.word x)) hx).cons
        (binding := .scalar (.word second)) (value := .scalar (.word y)) hy)
  | @applyBoolean values index f expression native booleans function variables arguments =>
    rw [extractScalarStepWith, bindings.noWordFunctionOfBoolean function] at compiled
    cases found : locals[index]?.bind ScalarStepBinding.booleanFunction? with
    | none =>
      rw [found] at compiled
      have absent : locals[index]?.bind ScalarStepBinding.resultFunction? = none := by
        cases lookup : locals[index]? with
        | none => simp
        | some binding =>
          have matched := bindings _ binding _ lookup function
          cases binding <;> simp_all [ScalarStepBinding.Matches, ScalarStepBinding.resultFunction?]
      simp [absent] at compiled
    | some f =>
      rw [found, booleanLocalOperands_expr] at compiled
      simp only [bind, Option.bind_some, Option.bind_eq_some_iff] at compiled
      obtain ⟨condition, hc, ht⟩ := compiled
      have meaning := extractBooleanLocalWith_correct expression _ _ _ hc bindings.toScalar variables
        (fun operand member expression found => extractScalarExprWith_correct (arguments operand member) found bindings.toScalar)
      exact bindings.booleanFunction found function _ _ code (guardWord_correct meaning) ht
  | @apply values index f a x function argument =>
    rw [extractScalarStepWith] at compiled
    cases found : locals[index]?.bind (ScalarStepBinding.function? false) with
    | none =>
      rw [found] at compiled
      have absent := bindings.noResultFunction function
      simp [absent, bindings.noBooleanFunctionOfWord function] at compiled
    | some f =>
      rw [found] at compiled
      simp only [bind, Option.bind_eq_some_iff] at compiled
      obtain ⟨arg, ha, hc⟩ := compiled
      exact bindings.function found function arg _ code
        (extractScalarExprWith_correct argument ha bindings.toScalar) hc
  | unitApply unitForm function argument =>
    rw [extractScalarStepWith_unitApply] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, hc⟩ := compiled
    exact bindings.function (Option.bind_eq_some_iff.mpr hf) function arg _ code
      (extractScalarExprWith_correct argument ha bindings.toScalar) hc
  | letStepFn type function body ihf ihb =>
    rw [extractScalarStepWith_letStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro argument value target ha hc
    exact ihf value hc (bindings.cons ha)
  | letBooleanStepFn type function body ihf ihb =>
    rw [extractScalarStepWith_letBooleanStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro argument value target ha hc
    exact ihf value hc (bindings.cons ha)
  | letUnitStepFn type unitForm function body ihf ihb =>
    rw [extractScalarStepWith_letUnitStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro argument value target ha hc
    exact ihf value hc
      ((bindings.cons (binding := .scalar .unit) (value := .scalar .unit) trivial).cons ha)
  | applyResult function argument ih =>
    rw [extractScalarStepWith, bindings.noWordFunction function, bindings.noBooleanFunctionOfResult function] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, hc⟩ := compiled
    exact bindings.resultFunction (Option.bind_eq_some_iff.mpr hf) function arg _ code (ih ha bindings) hc
  | letResultFn input output function body ihf ihb =>
    rw [extractScalarStepWith_letResultFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro argument value target ha hc
    exact ihf value hc (bindings.cons ha)
  | resultVar present =>
    exact bindings.result (by simpa only [extractScalarStepWith] using compiled) present
  | idRun type _ ih => exact ih (by simpa only [extractScalarStepWith_idRun] using compiled) bindings
  | idPure type _ ih => exact ih (by simpa only [extractScalarStepWith_idPure] using compiled) bindings
  | letResult type value body ihv ihb =>
    rw [extractScalarStepWith_letResult] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hc⟩ := compiled
    exact ihb hc (bindings.cons (ihv hb bindings))
  | bindResult input output value body ihv ihb =>
    rw [extractScalarStepWith_bindResult] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hc⟩ := compiled
    exact ihb hc (bindings.cons (ihv hb bindings))
  | idLet _ ih => exact ih (by simpa only [extractScalarStepWith_idLet] using compiled) bindings
  | metadata _ ih => exact ih (by simpa only [extractScalarStepWith] using compiled) bindings

end LeanExe.Extract.Core
