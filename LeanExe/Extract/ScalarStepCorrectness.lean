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
  | letFn type function body ih =>
    rw [extractScalarStepWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ih ht
    apply bindings.cons
    intro argument value target ha hc
    exact extractScalarExprWith_correct (function value) hc (bindings.toScalar.cons ha)
  | letUnitFn type function body ih =>
    rw [extractScalarStepWith_letUnitFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ih ht
    apply bindings.cons
    intro argument value target ha hc
    exact extractScalarExprWith_correct (function value) hc
      ((bindings.toScalar.cons (binding := .unit) (value := .unit) trivial).cons ha)
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
  | @apply values index f a x function argument =>
    rw [extractScalarStepWith] at compiled
    cases found : locals[index]?.bind (ScalarStepBinding.function? false) with
    | none =>
      rw [found] at compiled
      have absent := bindings.noResultFunction function
      simp [absent] at compiled
    | some f =>
      rw [found] at compiled
      simp only [bind, Option.bind_eq_some_iff] at compiled
      obtain ⟨arg, ha, hc⟩ := compiled
      exact bindings.function found function arg _ code
        (extractScalarExprWith_correct argument ha bindings.toScalar) hc
  | unitApply function argument =>
    rw [extractScalarStepWith] at compiled
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
  | letUnitStepFn type function body ihf ihb =>
    rw [extractScalarStepWith_letUnitStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro argument value target ha hc
    exact ihf value hc
      ((bindings.cons (binding := .scalar .unit) (value := .scalar .unit) trivial).cons ha)
  | applyResult function argument ih =>
    rw [extractScalarStepWith, bindings.noWordFunction function] at compiled
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
  | metadata _ ih => exact ih (by simpa only [extractScalarStepWith] using compiled) bindings

end LeanExe.Extract.Core
