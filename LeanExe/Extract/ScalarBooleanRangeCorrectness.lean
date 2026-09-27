import LeanExe.Extract.ScalarBooleanRangeChoice
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
  | case1 locals source value matched =>
    cases compiled
    obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨flag, .scalar evaluated, ScalarRangeExitPlan.scalar_meaning (fun accumulator index stop done =>
      extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))⟩
  | case2 locals name value body nondep bound matched notScalar ih =>
    obtain ⟨x, hx⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    obtain ⟨flag, evaluated, meaning⟩ := ih (.word x :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (bindings.bind hx matched) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨flag, .letBefore hx evaluated, meaning⟩
  | case3 locals name value body nondep notPure notScalar =>
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
  | case4 locals name value body nondep notScalar bodyIH valueIH =>
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, result, hp, hr, rfl⟩
    · obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      have extended : RangeExitBindingsMatch (.boolean bound :: locals) (.boolean flag :: values) saved := by
        intro accumulator index stop done
        exact (bindings accumulator index stop done).cons
          (extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))
      obtain ⟨result, continuation, meaning⟩ := bodyIH bound (.boolean flag :: values) hc
        (by simp [Value.kind, ScalarBinding.kind, typed]) extended (by
          intro binding member
          rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)
      exact ⟨result, .letFlagBefore evaluated continuation, meaning⟩
    · obtain ⟨flag, evaluated, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
        valueIH values hp typed bindings total
      obtain ⟨encoded, continuation⟩ := (extractScalarExprWith_supported hr).evaluates
        (.boolean flag :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
      obtain ⟨result, rfl⟩ := continuation.booleanConversion_result
      refine ⟨result, .letFlagResult evaluated continuation, stop, start, step, countEval, initialEval, stepEval, ?_⟩
      intro exitFlag
      exact extractScalarExprWith_correct continuation hr
        ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
  | case5 locals name type value body nondep notScalar ih =>
    obtain ⟨flag, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨flag, .idLet type evaluated, meaning⟩
  | case6 => contradiction
  | case7 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord notMany helper parsed notScalar ih =>
    rw [booleanBinaryHelper_sound parsed]
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    have supported := extractScalarExprWith_supported validated
    have native : ∀ x y, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) helper.body) (.word y :: .word x :: values) flag.toUInt64 := by
      intro x y
      obtain ⟨encoded, evaluated⟩ := supported.evaluates (.word y :: .word x :: values)
        (by simp [Value.kind, ScalarBinding.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x y => (native x y).choose
    obtain ⟨result, evaluated, meaning⟩ := ih (.binaryPredicateFunction f :: values) compiled
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
    exact ⟨result, .letBinaryPredicate helper (fun x y => (native x y).choose_spec) evaluated, meaning⟩
  | case8 => contradiction
  | case9 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord shape parsed checked validated notScalar ih =>
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
  | case10 => contradiction
  | case11 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type parsed checked validated notScalar ih =>
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
  | case12 => contradiction
  | case13 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary notWord type parsed notScalar enclosingIH directIH branchIH =>
    rcases scalarBooleanRangeCompleteContinuation_success compiled with previous |
      ⟨view, parsedChoice, guard, first, second, matched, ht, he, samePlan⟩
    · rcases scalarBooleanRangeContinuation_success previous with
        ⟨expression, checked, sameValue, validated, emitted⟩ | ⟨call, argument, bound, sameBody, validated, emitted⟩
      · have sameType := booleanType_sound parsed
        subst resultType
        subst value
        have supported := extractScalarExprWith_supported validated
        have native : ∀ x : UInt64, ∃ flag : Bool,
            EvalWith (.app (.const ``Bool.toUInt64 []) expression) (.word x :: values) flag.toUInt64 := by
          intro x
          obtain ⟨encoded, evaluated⟩ := supported.evaluates (.word x :: values)
            (by simp [Value.kind, booleanRangeInput, ScalarBinding.kind, typed])
          obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
          exact ⟨flag, evaluated⟩
        let f := fun x => (native x).choose
        obtain ⟨flag, evaluated, meaning⟩ := enclosingIH _ (.predicateFunction f :: values) emitted
          (by simp [Value.kind, booleanRangeInput, booleanRangePredicate, ScalarBinding.kind, typed]) (by
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
      · have sameType := booleanType_sound parsed
        subst resultType
        subst body
        obtain ⟨x, hx⟩ := (extractScalarExprWith_supported validated).evaluates values typed
        obtain ⟨flag, evaluated, meaning⟩ := directIH _ (.word x :: values) emitted
          (by simp [Value.kind, booleanRangeInput, ScalarBinding.kind, typed]) (bindings.bind hx validated) (by
            intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member)
        exact ⟨flag, .applyWord ⟨name, typeName, typeBi, paramBi, type, nondep⟩ call hx evaluated, meaning⟩
    · have sameType := booleanType_sound parsed
      subst resultType
      have shape := booleanFunctionChoice_sound parsedChoice
      subst body
      subst plan
      obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      have stable : ∀ accumulator index stop done,
          guard.ScalarEval (LeanExe.IR.rangeExitStore saved accumulator index stop done) flag.toUInt64
            (LeanExe.IR.rangeExitStore saved accumulator index stop done) := by
        intro accumulator index stop done
        exact extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done)
      cases flag with
      | false =>
        obtain ⟨result, branch, meaning⟩ := branchIH view.no (booleanFunctionChoice_sizes parsedChoice).2
          values he typed bindings total
        exact ⟨result, .wordFunctionChoice ⟨name, typeName, typeBi, paramBi, type, nondep⟩ view evaluated branch,
          ScalarRangeExitPlan.choice_meaning stable meaning⟩
      | true =>
        obtain ⟨result, branch, meaning⟩ := branchIH view.yes (booleanFunctionChoice_sizes parsedChoice).1
          values ht typed bindings total
        exact ⟨result, .wordFunctionChoice ⟨name, typeName, typeBi, paramBi, type, nondep⟩ view evaluated branch,
          ScalarRangeExitPlan.choice_meaning stable meaning⟩
  | case14 => contradiction
  | case15 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary type parsed checked validated notScalar ih =>
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
  | case16 => contradiction
  | case17 locals name typeName resultType typeBi paramName value paramBi body nondep notWord type parsed notScalar enclosingIH directIH branchIH =>
    rcases scalarBooleanRangeCompleteContinuation_success compiled with previous |
      ⟨view, parsedChoice, guard, first, second, matched, ht, he, samePlan⟩
    · rcases scalarBooleanRangeContinuation_success previous with
        ⟨expression, checked, sameValue, validated, emitted⟩ | ⟨call, argument, bound, sameBody, validated, emitted⟩
      · have sameType := booleanType_sound parsed
        subst resultType
        subst value
        have supported := extractScalarExprWith_supported validated
        have native : ∀ x : Bool, ∃ flag : Bool,
            EvalWith (.app (.const ``Bool.toUInt64 []) expression) (.boolean x :: values) flag.toUInt64 := by
          intro x
          obtain ⟨encoded, evaluated⟩ := supported.evaluates (.boolean x :: values)
            (by simp [Value.kind, booleanRangeInput, ScalarBinding.kind, typed])
          obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
          exact ⟨flag, evaluated⟩
        let f := fun x => (native x).choose
        obtain ⟨flag, evaluated, meaning⟩ := enclosingIH _ (.booleanPredicateFunction f :: values) emitted
          (by simp [Value.kind, booleanRangeInput, booleanRangePredicate, ScalarBinding.kind, typed]) (by
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
      · have sameType := booleanType_sound parsed
        subst resultType
        subst body
        obtain ⟨encoded, hx⟩ := (extractScalarExprWith_supported validated).evaluates values typed
        obtain ⟨flag, rfl⟩ := hx.booleanConversion_result
        have extended : RangeExitBindingsMatch (.boolean bound :: locals) (.boolean flag :: values) saved := by
          intro accumulator index stop done
          exact (bindings accumulator index stop done).cons
            (extractScalarExprWith_correct hx validated (bindings accumulator index stop done))
        obtain ⟨result, evaluated, meaning⟩ := directIH _ (.boolean flag :: values) emitted
          (by simp [Value.kind, booleanRangeInput, ScalarBinding.kind, typed]) extended (by
            intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member)
        exact ⟨result, .applyBoolean ⟨name, typeName, typeBi, paramBi, type, nondep⟩ call hx evaluated, meaning⟩
    · have sameType := booleanType_sound parsed
      subst resultType
      have shape := booleanFunctionChoice_sound parsedChoice
      subst body
      subst plan
      obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      have stable : ∀ accumulator index stop done,
          guard.ScalarEval (LeanExe.IR.rangeExitStore saved accumulator index stop done) flag.toUInt64
            (LeanExe.IR.rangeExitStore saved accumulator index stop done) := by
        intro accumulator index stop done
        exact extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done)
      cases flag with
      | false =>
        obtain ⟨result, branch, meaning⟩ := branchIH view.no (booleanFunctionChoice_sizes parsedChoice).2
          values he typed bindings total
        exact ⟨result, .booleanFunctionChoice ⟨name, typeName, typeBi, paramBi, type, nondep⟩ view evaluated branch,
          ScalarRangeExitPlan.choice_meaning stable meaning⟩
      | true =>
        obtain ⟨result, branch, meaning⟩ := branchIH view.yes (booleanFunctionChoice_sizes parsedChoice).1
          values ht typed bindings total
        exact ⟨result, .booleanFunctionChoice ⟨name, typeName, typeBi, paramBi, type, nondep⟩ view evaluated branch,
          ScalarRangeExitPlan.choice_meaning stable meaning⟩
  | case18 => contradiction
  | case19 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed checked validated notScalar ih =>
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
  | case20 => contradiction
  | case21 => contradiction
  | case22 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed checked validated notScalar ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x : UInt64) := supported.evaluates (.word x :: .unit :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.function true f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          (((bindings accumulator index stop exitFlag).cons (binding := .unit) (value := .unit) trivial).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.word argument :: .unit :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letUnitFn type .unit (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case23 => contradiction
  | case24 => contradiction
  | case25 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed checked validated notScalar ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x : UInt64) := supported.evaluates (.word x :: .unit :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.function true f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          (((bindings accumulator index stop exitFlag).cons (binding := .unit) (value := .unit) trivial).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.word argument :: .unit :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letUnitFn type .punit (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case26 locals name typeName resultType typeBi paramName input value paramBi body nondep notScalar ih =>
    obtain ⟨flag, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨flag, .idFunctionInput input resultType evaluated, meaning⟩
  | case27 => contradiction
  | case28 => contradiction
  | case29 locals input output value name domain body binder notWord types parsed notScalar bodyIH valueIH =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeFlagBindTypes_sound parsed
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, result, hp, hr, rfl⟩
    · obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      have extended : RangeExitBindingsMatch (.boolean bound :: locals) (.boolean flag :: values) saved := by
        intro accumulator index stop done
        exact (bindings accumulator index stop done).cons
          (extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))
      obtain ⟨result, continuation, meaning⟩ := bodyIH bound (.boolean flag :: values) hc
        (by simp [Value.kind, ScalarBinding.kind, typed]) extended (by
          intro binding member
          rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)
      exact ⟨result, .bindFlagBefore types.1 types.2 evaluated continuation, meaning⟩
    · obtain ⟨flag, evaluated, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
        valueIH values hp typed bindings total
      obtain ⟨encoded, continuation⟩ := (extractScalarExprWith_supported hr).evaluates
        (.boolean flag :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
      obtain ⟨result, rfl⟩ := continuation.booleanConversion_result
      refine ⟨result, .bindFlagResult types.1 types.2 evaluated continuation, stop, start, step, countEval, initialEval, stepEval, ?_⟩
      intro exitFlag
      exact extractScalarExprWith_correct continuation hr
        ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
  | case30 locals input output value name domain body binder types parsed bound matched notScalar ih =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    obtain ⟨x, hx⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    obtain ⟨flag, evaluated, meaning⟩ := ih (.word x :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (bindings.bind hx matched) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨flag, .bindBefore types.1 types.2 hx evaluated, meaning⟩
  | case31 locals input output value name domain body binder types parsed notPure notScalar =>
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
  | case32 => contradiction
  | case33 => contradiction
  | case34 locals type condition evidence yes no resultType parsed guard matched notScalar yesIH noIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, ht, second, he, rfl⟩ := compiled
    have same := booleanType_sound parsed
    subst type
    obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    obtain ⟨yesResult, yesEval, yesMeaning⟩ := scalarBooleanRangeArm_correct saved values ht typed bindings
      (fun plan h => yesIH values h typed bindings total)
    obtain ⟨noResult, noEval, noMeaning⟩ := scalarBooleanRangeArm_correct saved values he typed bindings
      (fun plan h => noIH values h typed bindings total)
    have stable : ∀ accumulator index stop done,
        guard.ScalarEval (LeanExe.IR.rangeExitStore saved accumulator index stop done) flag.toUInt64
          (LeanExe.IR.rangeExitStore saved accumulator index stop done) := by
      intro accumulator index stop done
      exact extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done)
    cases flag with
    | false =>
      rcases noEval with scalar | range
      · exact ⟨noResult, .choiceScalar resultType evaluated scalar,
          ScalarRangeExitPlan.choice_meaning stable noMeaning⟩
      · exact ⟨noResult, .choice resultType evaluated range,
          ScalarRangeExitPlan.choice_meaning stable noMeaning⟩
    | true =>
      rcases yesEval with scalar | range
      · exact ⟨yesResult, .choiceScalar resultType evaluated scalar,
          ScalarRangeExitPlan.choice_meaning stable yesMeaning⟩
      · exact ⟨yesResult, .choice resultType evaluated range,
          ScalarRangeExitPlan.choice_meaning stable yesMeaning⟩
  | case35 locals source notLet notFlag notIdLet notBinaryFunction notFunction notBooleanFunction notUnitFunction notPUnitFunction notIdFunction notBind notIf wrapper body parsed notScalar ih =>
    obtain ⟨flag, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨flag, booleanRangeWrapper_sound parsed ▸ BooleanRange.Eval.wrapped wrapper evaluated, meaning⟩
  | case36 =>
    obtain ⟨flag, evaluated, meaning⟩ := extractScalarBooleanAccumulatorWith_correct compiled typed bindings
    exact ⟨flag, .accumulator evaluated, meaning⟩

end LeanExe.Extract.Core
