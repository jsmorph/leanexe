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
  | case4 locals input output value name domain body binder types parsed bound matched ih =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    obtain ⟨x, hx⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    obtain ⟨flag, evaluated, meaning⟩ := ih (.word x :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (bindings.bind hx matched) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨flag, .bindBefore types.1 types.2 hx evaluated, meaning⟩
  | case5 locals input output value name domain body binder types parsed notPure =>
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
  | case6 locals source notLet notBind wrapper body parsed ih =>
    obtain ⟨flag, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨flag, booleanRangeWrapper_sound parsed ▸ BooleanRange.Eval.wrapped wrapper evaluated, meaning⟩
  | case7 => contradiction

end LeanExe.Extract.Core
