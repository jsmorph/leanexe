import LeanExe.Extract.ScalarBooleanRange
import LeanExe.Extract.ScalarRangeExitCorrectness

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- A Boolean continuation preserves the loop computation and normalizes its result. -/
theorem extractScalarBooleanRangeWith_correct {source : Lean.Expr} {locals : List ScalarBinding}
    {plan : ScalarRangeExitPlan} (saved : List UInt64) (values : List Value)
    (compiled : extractScalarBooleanRangeWith locals saved.length source = some plan)
    (typed : values.map Value.kind = locals.map ScalarBinding.kind)
    (bindings : RangeExitBindingsMatch locals values saved)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ flag, BooleanRange.Eval source values flag ∧ plan.Meaning saved flag.toUInt64 := by
  fun_induction extractScalarBooleanRangeWith locals saved.length source generalizing values plan with
  | case1 locals name value body nondep bound matched ih =>
    obtain ⟨x, hx⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    obtain ⟨flag, evaluated, meaning⟩ := ih (.word x :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (bindings.bind hx matched) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨flag, .letBefore hx evaluated, meaning⟩
  | case2 locals name value body nondep notPure =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, result, hr, rfl⟩ := compiled
    obtain ⟨x, hx, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
      extractScalarRangeExitWith_correct saved values hp typed bindings total
    have supported := extractScalarExprWith_supported hr
    obtain ⟨y, hy⟩ := supported.evaluates (.word x :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
    obtain ⟨flag, rfl⟩ := hy.booleanConversion_result
    refine ⟨flag, .letResult hx hy, stop, start, step, countEval, initialEval, stepEval, ?_⟩
    intro exitFlag
    exact extractScalarExprWith_correct hy hr
      ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
  | case3 => contradiction
  | case4 locals name value body nondep bound matched ih =>
    obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    have extended : RangeExitBindingsMatch (.boolean bound :: locals) (.boolean flag :: values) saved := by
      intro accumulator index stop done
      exact (bindings accumulator index stop done).cons
        (extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))
    obtain ⟨result, body, meaning⟩ := ih (.boolean flag :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) extended (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨result, .letFlagBefore evaluated body, meaning⟩
  | case5 locals name type value body nondep ih =>
    obtain ⟨flag, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨flag, .idLet type evaluated, meaning⟩
  | case6 => contradiction
  | case7 => contradiction
  | case8 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord shape parsed checked validated ih =>
    obtain ⟨sameType, sameValue⟩ := scalarManyFunction_sound parsed
    have supported := extractScalarExprWith_supported validated
    have function : SupportedWith (List.replicate shape.arity .word ++ locals.map ScalarBinding.kind) shape.body := by
      simpa [ScalarBinding.kind] using supported
    obtain ⟨f, meanings⟩ := function.manyFunction_evaluates values typed
    obtain ⟨flag, evaluated, meaning⟩ := ih (.manyFunction shape.arity f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro arguments native target len argumentsMeaning hc
        exact extractScalarExprWith_correct (meanings native (argumentsMeaning.length.symm.trans len)) hc
          ((bindings accumulator index stop exitFlag).words argumentsMeaning.reverse)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro arguments len
          exact extractScalarExprWith_accepts function (arguments.reverse.map ScalarBinding.word ++ locals)
            (by simp [List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const', len])
            (scalarWords_total _ total)
        · exact total binding member)
    rw [sameType, sameValue]
    exact ⟨flag, .letManyFn shape meanings evaluated, meaning⟩
  | case9 => contradiction
  | case10 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type parsed checked validated ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x y : UInt64) := supported.evaluates (.word y :: .word x :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x y => (native x y).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.binaryFunction f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro first x second y target hx hy hc
        exact extractScalarExprWith_correct ((native x y).choose_spec) hc
          (((bindings accumulator index stop exitFlag).cons (binding := .word first) (value := .word x) hx).cons
            (binding := .word second) (value := .word y) hy)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro first second
          apply extractScalarExprWith_accepts supported (.word second :: .word first :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letBinaryFn type (fun x y => (native x y).choose_spec) evaluated, meaning⟩
  | case11 => contradiction
  | case12 => contradiction
  | case13 => contradiction
  | case14 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary notWord type parsed expression parsedExpression checked validated ih =>
    have sameType := booleanType_sound parsed
    have sameValue := booleanLocalOperands_sound parsedExpression
    subst resultType
    subst value
    have supported := extractScalarExprWith_supported validated
    have native : ∀ x : UInt64, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr) (.word x :: values) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := supported.evaluates (.word x :: values)
        (by simp [Value.kind, ScalarBinding.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.predicateFunction f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          ((bindings accumulator index stop exitFlag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.word argument :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letPredicateFn expression type (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case15 => contradiction
  | case16 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary type parsed checked validated ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x : UInt64) := supported.evaluates (.word x :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.function false f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          ((bindings accumulator index stop exitFlag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.word argument :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letFn type (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case17 => contradiction
  | case18 => contradiction
  | case19 => contradiction
  | case20 locals name typeName resultType typeBi paramName value paramBi body nondep notWord type parsed expression parsedExpression checked validated ih =>
    have sameType := booleanType_sound parsed
    have sameValue := booleanLocalOperands_sound parsedExpression
    subst resultType
    subst value
    have supported := extractScalarExprWith_supported validated
    have native : ∀ x : Bool, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr) (.boolean x :: values) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := supported.evaluates (.boolean x :: values)
        (by simp [Value.kind, ScalarBinding.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.booleanPredicateFunction f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          ((bindings accumulator index stop exitFlag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.boolean argument :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letBooleanPredicateFn expression type (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case21 => contradiction
  | case22 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed checked validated ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x : Bool) := supported.evaluates (.boolean x :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.booleanFunction f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          ((bindings accumulator index stop exitFlag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.boolean argument :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letBooleanFn type (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case23 locals name typeName resultType typeBi paramName input value paramBi body nondep ih =>
    obtain ⟨flag, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨flag, .idFunctionInput input resultType evaluated, meaning⟩
  | case24 => contradiction
  | case25 => contradiction
  | case26 => contradiction
  | case27 locals input output value name domain body binder notWord types parsed bound matched ih =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeFlagBindTypes_sound parsed
    obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    have extended : RangeExitBindingsMatch (.boolean bound :: locals) (.boolean flag :: values) saved := by
      intro accumulator index stop done
      exact (bindings accumulator index stop done).cons
        (extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))
    obtain ⟨result, body, meaning⟩ := ih (.boolean flag :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) extended (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨result, .bindFlagBefore types.1 types.2 evaluated body, meaning⟩
  | case28 locals input output value name domain body binder types parsed bound matched ih =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    obtain ⟨x, hx⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    obtain ⟨flag, evaluated, meaning⟩ := ih (.word x :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (bindings.bind hx matched) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨flag, .bindBefore types.1 types.2 hx evaluated, meaning⟩
  | case29 locals input output value name domain body binder types parsed notPure =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, result, hr, rfl⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    obtain ⟨x, hx, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
      extractScalarRangeExitWith_correct saved values hp typed bindings total
    have supported := extractScalarExprWith_supported hr
    obtain ⟨y, hy⟩ := supported.evaluates (.word x :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
    obtain ⟨flag, rfl⟩ := hy.booleanConversion_result
    refine ⟨flag, .bindResult types.1 types.2 hx hy, stop, start, step, countEval, initialEval, stepEval, ?_⟩
    intro exitFlag
    exact extractScalarExprWith_correct hy hr
      ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
  | case30 locals source notLet notFlag notIdLet notBinaryFunction notFunction notBooleanFunction notIdFunction notBind wrapper body parsed ih =>
    obtain ⟨flag, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨flag, booleanRangeWrapper_sound parsed ▸ BooleanRange.Eval.wrapped wrapper evaluated, meaning⟩
  | case31 => contradiction

end LeanExe.Extract.Core
