import LeanExe.Extract.ScalarBooleanRangeChoice
import LeanExe.Extract.ScalarBooleanRange
import LeanExe.Extract.ScalarRangeExitInvariant

namespace LeanExe.Extract.Core

/-- The loop and converted Boolean continuation preserve every scalar invariant. -/
theorem extractScalarBooleanRangeWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {slot : Nat} (accumulator : P (.local slot)) (index : P (.local (slot + 1)))
    {source : Lean.Expr} {locals : List ScalarBinding} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanRangeWith locals slot source = some plan)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : plan.Holds P := by
  fun_induction extractScalarBooleanRangeWith locals slot source generalizing plan with
  | case1 locals name value body nondep bound matched ih =>
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact extractScalarExprWith_invariant P literal binary choice matched bindings
    · exact bindings binding member
  | case2 locals name value body nondep notPure =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, result, hr, rfl⟩ := compiled
    obtain ⟨count, initial, step, done, tail⟩ :=
      extractScalarRangeExitWith_invariant P literal binary choice accumulator index hp bindings
    refine ⟨count, initial, step, done, ?_⟩
    apply extractScalarExprWith_invariant P literal binary choice hr
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact tail
    · exact bindings binding member
  | case3 => contradiction
  | case4 locals name value body nondep bound matched ih =>
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact extractScalarExprWith_invariant P literal binary choice matched bindings
    · exact bindings binding member
  | case5 locals name type value body nondep ih => exact ih compiled bindings
  | case6 => contradiction
  | case7 => contradiction
  | case8 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord shape parsed checked validated ih =>
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro arguments target len holds extracted
      exact extractScalarExprWith_invariant P literal binary choice extracted (scalarWords_holds
        (fun argument member => holds argument (by simpa using member)) bindings)
    · exact bindings binding member
  | case9 => contradiction
  | case10 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type parsed checked validated ih =>
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro first second target firstValid secondValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact secondValid
      rcases List.mem_cons.mp member with rfl | member
      · exact firstValid
      · exact bindings binding member
    · exact bindings binding member
  | case11 => contradiction
  | case12 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary notWord type parsed enclosingIH directIH =>
    rcases scalarBooleanRangeContinuation_success compiled with
      ⟨expression, checked, sameValue, validated, emitted⟩ | ⟨argument, bound, sameBody, validated, emitted⟩
    · apply enclosingIH _ emitted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · intro argument target argumentValid extracted
        apply extractScalarExprWith_invariant P literal binary choice extracted
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact argumentValid
        · exact bindings binding member
      · exact bindings binding member
    · apply directIH _ emitted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact extractScalarExprWith_invariant P literal binary choice validated bindings
      · exact bindings binding member
  | case13 => contradiction
  | case14 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary type parsed checked validated ih =>
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      · exact bindings binding member
    · exact bindings binding member
  | case15 => contradiction
  | case16 locals name typeName resultType typeBi paramName value paramBi body nondep notWord type parsed enclosingIH directIH =>
    rcases scalarBooleanRangeContinuation_success compiled with
      ⟨expression, checked, sameValue, validated, emitted⟩ | ⟨argument, bound, sameBody, validated, emitted⟩
    · apply enclosingIH _ emitted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · intro argument target argumentValid extracted
        apply extractScalarExprWith_invariant P literal binary choice extracted
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact argumentValid
        · exact bindings binding member
      · exact bindings binding member
    · apply directIH _ emitted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact extractScalarExprWith_invariant P literal binary choice validated bindings
      · exact bindings binding member
  | case17 => contradiction
  | case18 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed checked validated ih =>
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      · exact bindings binding member
    · exact bindings binding member
  | case19 => contradiction
  | case20 => contradiction
  | case21 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed checked validated ih =>
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact bindings binding member
    · exact bindings binding member
  | case22 => contradiction
  | case23 => contradiction
  | case24 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed checked validated ih =>
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact bindings binding member
    · exact bindings binding member
  | case25 locals name typeName resultType typeBi paramName input value paramBi body nondep ih =>
    exact ih compiled bindings
  | case26 => contradiction
  | case27 => contradiction
  | case28 => contradiction
  | case29 locals input output value name domain body binder notWord types parsed bound matched ih =>
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact extractScalarExprWith_invariant P literal binary choice matched bindings
    · exact bindings binding member
  | case30 locals input output value name domain body binder types parsed bound matched ih =>
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact extractScalarExprWith_invariant P literal binary choice matched bindings
    · exact bindings binding member
  | case31 locals input output value name domain body binder types parsed notPure =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, result, hr, rfl⟩ := compiled
    obtain ⟨count, initial, step, done, tail⟩ :=
      extractScalarRangeExitWith_invariant P literal binary choice accumulator index hp bindings
    refine ⟨count, initial, step, done, ?_⟩
    apply extractScalarExprWith_invariant P literal binary choice hr
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact tail
    · exact bindings binding member
  | case32 => contradiction
  | case33 => contradiction
  | case34 locals type condition evidence yes no resultType parsed guard matched yesIH noIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, ht, second, he, rfl⟩ := compiled
    exact ScalarRangeExitPlan.choice_holds P literal choice
      (extractScalarExprWith_invariant P literal binary choice matched bindings)
      (scalarBooleanRangeArm_invariant P literal binary choice ht bindings (fun plan h => yesIH h bindings))
      (scalarBooleanRangeArm_invariant P literal binary choice he bindings (fun plan h => noIH h bindings))
  | case35 locals source notLet notFlag notIdLet notBinaryFunction notFunction notBooleanFunction notUnitFunction notPUnitFunction notIdFunction notBind notIf wrapper body parsed ih => exact ih compiled bindings
  | case36 => contradiction

end LeanExe.Extract.Core
