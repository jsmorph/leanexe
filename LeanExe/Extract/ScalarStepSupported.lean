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
  | case3 locals name value body nondep rejected =>
    rw [extractScalarStepWith, rejected] at compiled
    contradiction
  | case4 locals name value body nondep expression matched ihb =>
    have same := booleanLocalOperands_sound matched
    subst value
    rw [extractScalarStepWith_letBoolean] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    apply Step.Supported.letBoolean expression
    · rw [← scalarStepBindings_typed rfl]
      exact extractBooleanLocalWith_variables hc
    · intro operand member
      obtain ⟨target, found⟩ := extractBooleanLocalWith_operands hc operand member
      exact scalar found
    · simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb c ht
  | case5 locals name value body nondep ih =>
    rw [extractScalarStepWith_letE] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .letE (scalar hb) (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih bound ht)
  | case6 locals sourceType value name body bi rejected =>
    rw [extractScalarStepWith, rejected] at compiled
    contradiction
  | case7 locals sourceType value name body bi type matched rejected =>
    rw [extractScalarStepWith, matched, rejected] at compiled
    contradiction
  | case8 locals sourceType value name body bi type matched action parsed ihb =>
    have typeEq := scalarStepResultType_sound matched
    have valueEq := booleanAction_sound parsed
    subst sourceType value
    change extractScalarStepWith locals
      (BooleanIdentity.bind name bi action.expr body (Step.resultType type)) = some target at compiled
    rw [extractScalarStepWith_booleanBind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    apply Step.Supported.idBindBoolean action type
    · rw [← scalarStepBindings_typed rfl]
      exact extractBooleanLocalWith_variables hc
    · intro operand member
      obtain ⟨expression, found⟩ := extractBooleanLocalWith_operands hc operand member
      exact scalar found
    · simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb c ht
  | case9 locals sourceType value name body bi rejected =>
    rw [extractScalarStepWith, rejected] at compiled
    contradiction
  | case10 locals sourceType value name body bi type matched ih =>
    have typeEq := scalarStepResultType_sound matched
    subst sourceType
    change extractScalarStepWith locals (Step.bindWord name bi type value body) = some target at compiled
    rw [extractScalarStepWith_bind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .idBind type (scalar hb) (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih bound ht)
  | case11 locals type condition evidence t e rejected =>
    rw [extractScalarStepWith, rejected] at compiled
    contradiction
  | case12 locals type condition evidence t e result matched rejected rejectedGuard rejectedLocal =>
    rw [extractScalarStepWith, matched, rejected, rejectedGuard, rejectedLocal] at compiled
    contradiction
  | case13 locals sourceType condition evidence t e type typeMatched rejected rejectedGuard guard matched iht ihe =>
    have typeEq := scalarStepResultType_sound typeMatched
    subst sourceType
    obtain ⟨hc, he⟩ := booleanLocalGuard_sound matched
    subst condition evidence
    change extractScalarStepWith locals (guard.branch (Step.resultType type) t e) = some target at compiled
    rw [extractScalarStepWith_booleanBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, _⟩ := compiled
    apply Step.Supported.chooseBoolean guard type _ _ (iht ht) (ihe he)
    · rw [← scalarStepBindings_typed rfl]
      exact extractBooleanLocalWith_variables hc
    · intro operand member
      obtain ⟨expression, found⟩ := extractBooleanLocalWith_operands hc operand member
      exact scalar found
  | case14 locals sourceType condition evidence t e type typeMatched rejected guard matched iht ihe =>
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
  | case15 locals sourceType condition evidence t e type typeMatched op a b matched iht ihe =>
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
  | case16 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep noScalar noStep noMany noManyStep =>
    rw [extractScalarStepWith, noScalar, noStep, noMany, noManyStep] at compiled
    contradiction
  | case17 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep noScalar noStep noMany shape matched ih0 ihf ihb =>
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
  | case18 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep noScalar noStep shape matched ihb =>
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
  | case19 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep noScalar type matched ih0 ihf ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letBinaryStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letBinaryStepFn type (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case20 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type matched ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letBinaryFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    simp only [List.attach_map_val] at ihb
    exact .letBinaryFn type
      (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported hc)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb ht)
  | case21 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary type matched ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    simp only [List.attach_map_val] at ihb
    exact .letFn type
      (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported hc)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb ht)
  | case22 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary noScalar noStep noBoolean =>
    rw [extractScalarStepWith, noScalar, noStep, noBoolean] at compiled
    · contradiction
    · exact excludedBinary
  | case23 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary noScalar noStep type matched ihb =>
    rw [extractScalarStepWith, noScalar, noStep, matched] at compiled
    · simp only [bind, Option.bind_eq_some_iff] at compiled
      obtain ⟨boolean, parsed, checked, hc, ht⟩ := compiled
      have sameType := booleanType_sound matched
      have sameValue := booleanLocalOperands_sound parsed
      subst resultType
      subst value
      simp only [List.attach_map_val] at ihb
      exact .letPredicateFn boolean type
        (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractBooleanLocalWith_variables hc)
        (fun operand member => by
          obtain ⟨target, found⟩ := extractBooleanLocalWith_operands hc operand member
          simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported found)
        (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb boolean ht)
    · exact excludedBinary
  | case24 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary noScalar type matched ih0 ihf ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letStepFn type (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case25 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letUnitFn (unitForm := .unit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    simp only [List.attach_map_val] at ihb
    exact .letUnitFn type .unit
      (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported hc)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb ht)
  | case26 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep noScalar noStep =>
    rw [extractScalarStepWith, noScalar, noStep] at compiled
    contradiction
  | case27 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep noScalar type matched ih0 ihf ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letUnitStepFn (unitForm := .unit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letUnitStepFn type .unit (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case28 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letUnitFn (unitForm := .punit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    simp only [List.attach_map_val] at ihb
    exact .letUnitFn type .punit
      (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported hc)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb ht)
  | case29 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep noScalar noStep =>
    rw [extractScalarStepWith, noScalar, noStep] at compiled
    contradiction
  | case30 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep noScalar type matched ih0 ihf ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letUnitStepFn (unitForm := .punit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letUnitStepFn type .punit (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case31 locals index argument =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, _⟩ := compiled
    exact .unitApply .unit (scalarStepFunction_kind (Option.bind_eq_some_iff.mpr hf)) (scalar ha)
  | case32 locals index argument =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, _⟩ := compiled
    exact .unitApply .punit (scalarStepFunction_kind (Option.bind_eq_some_iff.mpr hf)) (scalar ha)
  | case33 locals index first second excludedUnit excludedPUnit =>
    rw [extractScalarStepWith_binaryApply _ _ _ _ (by
      intro unitForm; cases unitForm
      · exact excludedUnit
      · exact excludedPUnit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, a, ha, b, hb, _⟩ := compiled
    exact .binaryApply (scalarStepBinaryFunction_kind (Option.bind_eq_some_iff.mpr hf)) (scalar ha) (scalar hb)
  | case34 locals index argument f found =>
    rw [extractScalarStepWith, found] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨arg, ha, _⟩ := compiled
    exact .apply (scalarStepFunction_kind found) (scalar ha)
  | case35 locals index argument noWord f found =>
    rw [extractScalarStepWith, noWord, found] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsed, condition, hc, _⟩ := compiled
    have same := booleanLocalOperands_sound parsed
    subst argument
    apply Step.Supported.applyBoolean expression (scalarStepBooleanFunction_kind found)
    · rw [← scalarStepBindings_typed rfl]
      exact extractBooleanLocalWith_variables hc
    · intro operand member
      obtain ⟨target, found⟩ := extractBooleanLocalWith_operands hc operand member
      exact scalar found
  | case36 locals index argument absent noBoolean ih =>
    rw [extractScalarStepWith, absent, noBoolean] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, _⟩ := compiled
    exact .applyResult (scalarStepResultFunction_kind (Option.bind_eq_some_iff.mpr hf)) (ih ha)
  | case37 locals value =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, _⟩ := compiled
    exact .yieldDirect (scalar hv)
  | case38 locals value =>
    rw [extractScalarStepWith] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨value, hv, _⟩ := compiled
    exact .doneDirect (scalar hv)
  | case39 locals index =>
    exact .resultVar (scalarStepResult_kind (by simpa only [extractScalarStepWith] using compiled))
  | case40 locals type body rejected =>
    rw [extractScalarStepWith, rejected] at compiled
    contradiction
  | case41 locals sourceType body type matched ih =>
    have typeEq := scalarStepResultType_sound matched
    subst sourceType
    change extractScalarStepWith locals (Step.idRun type body) = some target at compiled
    exact .idRun type (ih (by simpa only [extractScalarStepWith_idRun] using compiled))
  | case42 locals name typeName resultType typeBi paramName value paramBi body nondep type matched ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letBooleanFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    simp only [List.attach_map_val] at ihb
    exact .letBooleanFn type
      (by simpa [ScalarBinding.kind, scalarStepBindings_typed rfl] using extractScalarExprWith_supported hc)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihb ht)
  | case43 locals name typeName resultType typeBi paramName value paramBi body nondep noScalar noStep =>
    rw [extractScalarStepWith, noScalar, noStep] at compiled
    contradiction
  | case44 locals name typeName resultType typeBi paramName value paramBi body nondep noScalar type matched ih0 ihf ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst resultType
    rw [extractScalarStepWith_letBooleanStepFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letBooleanStepFn type (by simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case45 locals name typeName sourceOutput typeBi paramName sourceInput value paramBi body nondep input output outputMatched noBinary noWord noUnit noPUnit noBoolean inputMatched ih0 ihf ihb =>
    have hi := scalarStepResultType_sound inputMatched
    have ho := scalarStepResultType_sound outputMatched
    subst sourceInput sourceOutput
    rw [extractScalarStepWith_letResultFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letResultFn input output (by simpa [ScalarStepBinding.kind] using ih0 hc)
      (by simpa [ScalarStepBinding.kind] using ihb ht)
  | case46 locals name typeName output typeBi paramName input value paramBi body nondep noBinary noWord noUnit noPUnit noBoolean rejected =>
    rw [extractScalarStepWith] at compiled <;> try assumption
    simp only [↓reduceIte] at compiled
    contradiction
  | case47 locals name typeName input output typeBi paramName domain value paramBi body nondep noBinary noWord noUnit noPUnit noBoolean different =>
    rw [extractScalarStepWith] at compiled <;> try assumption
    simp [different] at compiled
  | case48 locals name type value body nondep ih =>
    rw [extractScalarStepWith] at compiled
    exact .idLet (ih compiled)
  | case49 locals name sourceType value body nondep h0 h1 h2 h3 h4 h5 h6 h7 h8 rejected =>
    rw [extractScalarStepWith] at compiled <;> first | assumption | (rw [rejected] at compiled; contradiction)
  | case50 locals name sourceType value body nondep h0 h1 h2 h3 h4 h5 h6 h7 h8 type matched ihv ihb =>
    have typeEq := scalarStepResultType_sound matched
    subst sourceType
    rw [extractScalarStepWith_letResult] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .letResult type (ihv hb) (by simpa [ScalarStepBinding.kind] using ihb bound ht)
  | case51 locals sourceOutput value name sourceInput body bi input output outputMatched noBooleanBind excluded inputMatched ihv ihb =>
    have hi := scalarStepResultType_sound inputMatched
    have ho := scalarStepResultType_sound outputMatched
    subst sourceInput sourceOutput
    change extractScalarStepWith locals (Step.bindResult name bi input output value body) = some target at compiled
    rw [extractScalarStepWith_bindResult] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .bindResult input output (ihv hb) (by simpa [ScalarStepBinding.kind] using ihb bound ht)
  | case52 locals output value name input body bi noBooleanBind excluded rejected =>
    rw [extractScalarStepWith] at compiled <;> try assumption
    simp only [↓reduceIte] at compiled
    contradiction
  | case53 locals input output value name domain body bi noBooleanBind excluded different =>
    rw [extractScalarStepWith] at compiled <;> try assumption
    simp [different] at compiled
  | case54 locals data body ih =>
    exact .metadata (ih (by simpa only [extractScalarStepWith] using compiled))
  | case55 locals type condition evidence tn td t tb fn fd e fb rejected =>
    rw [extractScalarStepWith, rejected] at compiled
    contradiction
  | case56 locals type condition evidence tn td t tb fn fd e fb result matched rejected rejectedBoolean =>
    rw [extractScalarStepWith, matched, rejected, rejectedBoolean] at compiled
    contradiction
  | case57 locals sourceType condition evidence tn td t tb fn fd e fb type matched rejected guard parsed iht ihe =>
    have typeEq := scalarStepResultType_sound matched
    subst sourceType
    obtain ⟨hc, hd, htDomain, heDomain⟩ := booleanLocalDependentGuard_sound parsed
    subst condition evidence td fd
    change extractScalarStepWith locals (guard.dependentBranch (Step.resultType type) tn fn tb fb t e) = some target at compiled
    rw [extractScalarStepWith_booleanDependentBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, _⟩ := compiled
    apply Step.Supported.chooseBooleanDependent guard type tn fn tb fb
    · rw [← scalarStepBindings_typed rfl]
      exact extractBooleanLocalWith_variables hc
    · intro operand member
      obtain ⟨expression, found⟩ := extractBooleanLocalWith_operands hc operand member
      exact scalar found
    · simpa [ScalarStepBinding.kind, ScalarBinding.kind] using iht ht
    · simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihe he
  | case58 locals sourceType condition evidence tn td t tb fn fd e fb type matched guard parsed iht ihe =>
    have typeEq := scalarStepResultType_sound matched
    subst sourceType
    obtain ⟨hc, hd, htDomain, heDomain⟩ := dependentGuard_sound parsed
    subst condition evidence td fd
    change extractScalarStepWith locals (guard.dependentBranch (Step.resultType type) tn fn tb fb t e) = some target at compiled
    rw [extractScalarStepWith_dependentBranch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨c, hc, ti, ht, ei, he, _⟩ := compiled
    apply Step.Supported.chooseDependent guard type tn fn tb fb
    · intro operand member
      obtain ⟨expression, found⟩ := extractGuard_operands guard _ hc operand member
      exact scalar found
    · simpa [ScalarStepBinding.kind, ScalarBinding.kind] using iht ht
    · simpa [ScalarStepBinding.kind, ScalarBinding.kind] using ihe he
  | case59 locals head first second noPure noBooleanBind noWordBind noChoice noUnit noPUnit noBinary noYield noDone noRun noBind noDependent =>
    rw [extractScalarStepWith] at compiled
    · simp only [bind, Option.bind_eq_some_iff] at compiled
      obtain ⟨call, matched, f, hf, arguments, ha, _⟩ := compiled
      rw [scalarManyCall_sound matched]
      apply Step.Supported.manyApply call (scalarStepManyFunction_kind (Option.bind_eq_some_iff.mpr hf))
      intro operand member
      obtain ⟨expression, found⟩ := extractScalarArguments_operands call.arguments _ ha operand member
      exact scalar found
    all_goals assumption
  | case60 locals source hp hl hb hBooleanBind hc hf huf hpf hua hpa ha hdy hdd hv hr hrf hlr hbr hm happ =>
    rw [extractScalarStepWith] at compiled <;> first | assumption | contradiction

end LeanExe.Extract.Core
