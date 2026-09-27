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
  | case8 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed checked validated ih =>
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
  | case9 => contradiction
  | case10 => contradiction
  | case11 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed checked validated ih =>
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
  | case12 => contradiction
  | case13 => contradiction
  | case14 locals input output value name domain body binder notWord types parsed bound matched ih =>
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact extractScalarExprWith_invariant P literal binary choice matched bindings
    · exact bindings binding member
  | case15 locals input output value name domain body binder types parsed bound matched ih =>
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact extractScalarExprWith_invariant P literal binary choice matched bindings
    · exact bindings binding member
  | case16 locals input output value name domain body binder types parsed notPure =>
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
  | case17 locals source notLet notFlag notIdLet notFunction notBooleanFunction notBind wrapper body parsed ih => exact ih compiled bindings
  | case18 => contradiction

end LeanExe.Extract.Core
