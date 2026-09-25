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
  | case7 locals type condition evidence t e result matched rejected rejectedGuard =>
    rw [extractScalarStepWith, matched, rejected, rejectedGuard] at compiled
    contradiction
  | case8 locals sourceType condition evidence t e type typeMatched rejected guard matched iht ihe =>
    have typeEq := scalarStepResultType_sound typeMatched
    subst sourceType
    obtain ⟨hc, he⟩ := compoundGuard_sound matched
    subst condition evidence
    change Step.Supported _ (guard.branch (Step.resultType type) t e)
    change extractScalarStepWith locals (guard.branch (Step.resultType type) t e) = some target at compiled
    rw [extractScalarStepWith_compoundBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, _⟩ := compiled
    apply Step.Supported.chooseCompound guard type _ (iht ht) (ihe he)
    intro operand member
    obtain ⟨expression, found⟩ := extractGuard_operands guard.tree _ hc operand member
    exact scalar found
  | case9 locals sourceType condition evidence t e type typeMatched op a b matched iht ihe =>
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
  | case10 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep noScalar noStep noMany noManyStep =>
    rw [extractScalarStepWith, noScalar, noStep, noMany, noManyStep] at compiled
    contradiction
  | case11 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep noScalar noStep noMany shape matched ih0 ihf ihb =>
    obtain ⟨sameType, sameValue⟩ := scalarManyStepFunction_sound matched
    rw [sameType, sameValue] at compiled ⊢
    change Step.Supported _ (shape.bind name body nondep Step.resultType)
    change extractScalarStepWith locals (shape.bind name body nondep Step.resultType) = some target at compiled
    rw [extractScalarStepWith_letManyStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letManyStepFn shape
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case12 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep noScalar noStep shape matched ihb =>
    obtain ⟨sameType, sameValue⟩ := scalarManyFunction_sound matched
    rw [sameType, sameValue] at compiled ⊢
    change Step.Supported _ (shape.bind name body nondep)
    change extractScalarStepWith locals (shape.bind name body nondep) = some target at compiled
    rw [extractScalarStepWith_letManyFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    simp only [List.attach_map_val] at ihb
    exact .letManyFn shape
      (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported hc)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb ht)
  | case13 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep noScalar type matched ih0 ihf ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letBinaryStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letBinaryStepFn type (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case14 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type matched ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letBinaryFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    simp only [List.attach_map_val] at ihb
    exact .letBinaryFn type
      (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported hc)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb ht)
  | case15 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary type matched ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    simp only [List.attach_map_val] at ihb
    exact .letFn type
      (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported hc)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb ht)
  | case16 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary noScalar noStep =>
    rw [extractScalarStepWith, noScalar, noStep] at compiled
    · contradiction
    · exact excludedBinary
  | case17 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary noScalar type matched ih0 ihf ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letStepFn type (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case18 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letUnitFn (unitForm := .unit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    simp only [List.attach_map_val] at ihb
    exact .letUnitFn type .unit
      (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported hc)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb ht)
  | case19 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep noScalar noStep =>
    rw [extractScalarStepWith, noScalar, noStep] at compiled
    contradiction
  | case20 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep noScalar type matched ih0 ihf ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letUnitStepFn (unitForm := .unit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letUnitStepFn type .unit (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case21 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letUnitFn (unitForm := .punit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    simp only [List.attach_map_val] at ihb
    exact .letUnitFn type .punit
      (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported hc)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb ht)
  | case22 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep noScalar noStep =>
    rw [extractScalarStepWith, noScalar, noStep] at compiled
    contradiction
  | case23 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep noScalar type matched ih0 ihf ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letUnitStepFn (unitForm := .punit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letUnitStepFn type .punit (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case24 locals index argument =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, _⟩ := compiled
    exact .unitApply .unit (scalarStepFunction_kind (Option.bind_eq_some_iff.mpr hf)) (scalar ha)
  | case25 locals index argument =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, _⟩ := compiled
    exact .unitApply .punit (scalarStepFunction_kind (Option.bind_eq_some_iff.mpr hf)) (scalar ha)
  | case26 locals index first second excludedUnit excludedPUnit =>
    rw [extractScalarStepWith_binaryApply _ _ _ _ (by
      intro unitForm; cases unitForm
      · exact excludedUnit
      · exact excludedPUnit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, a, ha, b, hb, _⟩ := compiled
    exact .binaryApply (scalarStepBinaryFunction_kind (Option.bind_eq_some_iff.mpr hf)) (scalar ha) (scalar hb)
  | case27 locals index argument f found =>
    rw [extractScalarStepWith, found] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨arg, ha, _⟩ := compiled
    exact .apply (scalarStepFunction_kind found) (scalar ha)
  | case28 locals index argument absent ih =>
    rw [extractScalarStepWith, absent] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, _⟩ := compiled
    exact .applyResult (scalarStepResultFunction_kind (Option.bind_eq_some_iff.mpr hf)) (ih ha)
  | case29 locals value =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, _⟩ := compiled
    exact .yieldDirect (scalar hv)
  | case30 locals value =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, _⟩ := compiled
    exact .doneDirect (scalar hv)
  | case31 locals index =>
    exact .resultVar (scalarStepResult_kind (by simpa only [extractScalarStepWith] using compiled))
  | case32 locals type body rejected =>
    rw [extractScalarStepWith, rejected] at compiled
    contradiction
  | case33 locals sourceType body type matched ih =>
    have typeEq := scalarStepResultType_sound matched
    subst sourceType
    change extractScalarStepWith locals (Step.idRun type body) = some target at compiled
    exact .idRun type (ih (by simpa only [extractScalarStepWith_idRun] using compiled))
  | case34 locals name typeName sourceOutput typeBi paramName sourceInput value paramBi body nondep input output outputMatched noBinary noWord noUnit noPUnit inputMatched ih0 ihf ihb =>
    have hi := scalarStepResultType_sound inputMatched
    have ho := scalarStepResultType_sound outputMatched
    subst sourceInput sourceOutput
    rw [extractScalarStepWith_letResultFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letResultFn input output (by simpa [ScalarStepBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case35 locals name typeName output typeBi paramName input value paramBi body nondep noBinary noWord noUnit noPUnit rejected =>
    rw [extractScalarStepWith] at compiled <;> try assumption
    simp only [↓reduceIte] at compiled
    contradiction
  | case36 locals name typeName input output typeBi paramName domain value paramBi body nondep noBinary noWord noUnit noPUnit different =>
    rw [extractScalarStepWith] at compiled <;> try assumption
    simp [different] at compiled
  | case37 locals name sourceType value body nondep h1 h2 h3 h4 h5 h6 rejected =>
    rw [extractScalarStepWith] at compiled <;> first | assumption | (rw [rejected] at compiled; contradiction)
  | case38 locals name sourceType value body nondep h1 h2 h3 h4 h5 h6 type matched ihv ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst sourceType
    rw [extractScalarStepWith_letResult] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .letResult type (ihv hb) (by simpa [ScalarStepBinding.kind] using ihb bound ht)
  | case39 locals sourceOutput value name sourceInput body bi input output outputMatched excluded inputMatched ihv ihb =>
    have hi := scalarStepResultType_sound inputMatched
    have ho := scalarStepResultType_sound outputMatched
    subst sourceInput sourceOutput
    change extractScalarStepWith locals (Step.bindResult name bi input output value body) = some target at compiled
    rw [extractScalarStepWith_bindResult] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .bindResult input output (ihv hb) (by simpa [ScalarStepBinding.kind] using ihb bound ht)
  | case40 locals output value name input body bi excluded rejected =>
    rw [extractScalarStepWith] at compiled <;> try assumption
    simp only [↓reduceIte] at compiled
    contradiction
  | case41 locals input output value name domain body bi excluded different =>
    rw [extractScalarStepWith] at compiled <;> try assumption
    simp [different] at compiled
  | case42 locals data body ih =>
    exact .metadata (ih (by simpa only [extractScalarStepWith] using compiled))
  | case43 locals head first second noPure noWordBind noChoice noUnit noPUnit noBinary noYield noDone noRun noBind =>
    rw [extractScalarStepWith] at compiled
    · simp only [bind, Option.bind_eq_some_iff] at compiled
      obtain ⟨call, matched, f, hf, arguments, ha, _⟩ := compiled
      rw [scalarManyCall_sound matched]
      apply Step.Supported.manyApply call (scalarStepManyFunction_kind (Option.bind_eq_some_iff.mpr hf))
      intro operand member
      obtain ⟨expression, found⟩ := extractScalarArguments_operands call.arguments _ ha operand member
      exact scalar found
    all_goals assumption
  | case44 locals source hp hl hb hc hf huf hpf hua hpa ha hdy hdd hv hr hrf hlr hbr hm happ =>
    rw [extractScalarStepWith] at compiled <;> first | assumption | contradiction

end LeanExe.Extract.Core
