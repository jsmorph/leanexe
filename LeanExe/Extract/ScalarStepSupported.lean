import LeanExe.Extract.ScalarStepEquations

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Successful step extraction admits only the independent source grammar.
The dummy-argument checks also cover every unused local function body. -/
theorem extractScalarStepWith_supported {source : Lean.Expr} {locals : List ScalarStepBinding}
    {target : ScalarStepCode} (compiled : extractScalarStepWith locals source = some target) :
    Step.Supported (locals.map ScalarStepBinding.kind) source := by
  have scalar {locals : List ScalarStepBinding} {source : Lean.Expr} {target : LeanExe.IR.Expr}
      (compiled : extractScalarExprWith (locals.map ScalarStepBinding.toScalar) source = some target) :
      SupportedWith ((locals.map ScalarStepBinding.kind).map Step.BindingKind.toScalar) source := by
    rw [← scalarStepBindings_typed rfl]
    exact extractScalarExprWith_supported compiled
  induction locals, source using extractScalarStepWith.induct generalizing target with
  | case1 locals type body rejected =>
    rw [extractScalarStepWith, rejected] at compiled
    contradiction
  | case2 locals sourceType body type matched ih =>
    have typeEq := scalarStepResultType_sound matched
    subst sourceType
    change extractScalarStepWith locals (Step.idPure type body) = some target at compiled
    exact .idPure type (ih (by simpa only [extractScalarStepWith_idPure] using compiled))
  | case3 locals name value body nondep ih =>
    rw [extractScalarStepWith_letE] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .letE (scalar hb) (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih bound ht)
  | case4 locals sourceType value name body bi rejected =>
    rw [extractScalarStepWith, rejected] at compiled
    contradiction
  | case5 locals sourceType value name body bi type matched ih =>
    have typeEq := scalarStepResultType_sound matched
    subst sourceType
    change extractScalarStepWith locals (Step.bindWord name bi type value body) = some target at compiled
    rw [extractScalarStepWith_bind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .idBind type (scalar hb) (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih bound ht)
  | case6 locals type condition evidence t e rejected =>
    rw [extractScalarStepWith, rejected] at compiled
    contradiction
  | case7 locals type condition evidence t e result matched rejected =>
    rw [extractScalarStepWith, matched, rejected] at compiled
    contradiction
  | case8 locals sourceType condition evidence t e type typeMatched op a b matched iht ihe =>
    have typeEq := scalarStepResultType_sound typeMatched
    subst sourceType
    obtain ⟨hc, he⟩ := comparison_sound matched
    subst condition evidence
    change Step.Supported _ (Step.branch op type a b t e)
    change extractScalarStepWith locals (Step.branch op type a b t e) = some target at compiled
    rw [extractScalarStepWith_branch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨ai, ha, bi, hb, ti, ht, ei, he, _⟩ := compiled
    exact .choose op type (scalar ha) (scalar hb) (iht ht) (ihe he)
  | case9 locals name typeName resultType typeBi paramName value paramBi body nondep type matched ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    simp only [List.attach_map_val] at ihb
    exact .letFn type
      (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported hc)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb ht)
  | case10 locals name typeName resultType typeBi paramName value paramBi body nondep noScalar noStep =>
    rw [extractScalarStepWith, noScalar, noStep] at compiled
    contradiction
  | case11 locals name typeName resultType typeBi paramName value paramBi body nondep noScalar type matched ih0 ihf ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letStepFn type (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case12 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letUnitFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    simp only [List.attach_map_val] at ihb
    exact .letUnitFn type
      (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported hc)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb ht)
  | case13 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep noScalar noStep =>
    rw [extractScalarStepWith, noScalar, noStep] at compiled
    contradiction
  | case14 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep noScalar type matched ih0 ihf ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letUnitStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letUnitStepFn type (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case15 locals index argument =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, _⟩ := compiled
    exact .unitApply (scalarStepFunction_kind (Option.bind_eq_some_iff.mpr hf)) (scalar ha)
  | case16 locals index argument =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, _⟩ := compiled
    exact .apply (scalarStepFunction_kind (Option.bind_eq_some_iff.mpr hf)) (scalar ha)
  | case17 locals value =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, _⟩ := compiled
    exact .yieldDirect (scalar hv)
  | case18 locals value =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, _⟩ := compiled
    exact .doneDirect (scalar hv)
  | case19 locals index =>
    exact .resultVar (scalarStepResult_kind (by simpa only [extractScalarStepWith] using compiled))
  | case20 locals type body rejected =>
    rw [extractScalarStepWith, rejected] at compiled
    contradiction
  | case21 locals sourceType body type matched ih =>
    have typeEq := scalarStepResultType_sound matched
    subst sourceType
    change extractScalarStepWith locals (Step.idRun type body) = some target at compiled
    exact .idRun type (ih (by simpa only [extractScalarStepWith_idRun] using compiled))
  | case22 locals name sourceType value body nondep h1 h2 h3 rejected =>
    rw [extractScalarStepWith] at compiled <;> first | assumption | (rw [rejected] at compiled; contradiction)
  | case23 locals name sourceType value body nondep h1 h2 h3 type matched ihv ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst sourceType
    rw [extractScalarStepWith_letResult] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .letResult type (ihv hb) (by simpa [ScalarStepBinding.kind] using ihb bound ht)
  | case24 locals sourceOutput value name sourceInput body bi input output outputMatched excluded inputMatched ihv ihb =>
    have hi := scalarStepResultType_sound inputMatched
    have ho := scalarStepResultType_sound outputMatched
    subst sourceInput sourceOutput
    change extractScalarStepWith locals (Step.bindResult name bi input output value body) = some target at compiled
    rw [extractScalarStepWith_bindResult] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .bindResult input output (ihv hb) (by simpa [ScalarStepBinding.kind] using ihb bound ht)
  | case25 locals output value name input body bi excluded rejected =>
    rw [extractScalarStepWith] at compiled <;> try assumption
    simp only [↓reduceIte] at compiled
    contradiction
  | case26 locals input output value name domain body bi excluded different =>
    rw [extractScalarStepWith] at compiled <;> try assumption
    simp [different] at compiled
  | case27 locals data body ih =>
    exact .metadata (ih (by simpa only [extractScalarStepWith] using compiled))
  | case28 locals source hp hl hb hc hf huf hua ha hdy hdd hv hr hlr hbr hm =>
    rw [extractScalarStepWith] at compiled <;> first | assumption | contradiction

end LeanExe.Extract.Core
