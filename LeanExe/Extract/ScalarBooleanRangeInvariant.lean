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
  | case1 name value body nondep =>
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
  | case2 input output value name domain body binder =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨⟨inputType, outputType⟩, types, before, hp, result, hr, rfl⟩ := compiled
    obtain ⟨count, initial, step, done, tail⟩ :=
      extractScalarRangeExitWith_invariant P literal binary choice accumulator index hp bindings
    refine ⟨count, initial, step, done, ?_⟩
    apply extractScalarExprWith_invariant P literal binary choice hr
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact tail
    · exact bindings binding member
  | case3 source notLet notBind wrapper body parsed ih => exact ih compiled
  | case4 => contradiction

end LeanExe.Extract.Core
