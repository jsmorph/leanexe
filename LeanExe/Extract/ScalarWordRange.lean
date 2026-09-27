import LeanExe.Extract.ScalarBooleanWordRange
import LeanExe.Source.ScalarWordRange

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Select a checked scalar or loop plan, or recursively compile word branches. -/
def extractScalarWordRangeWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
  match extractScalarExprWith locals source with
  | some value => some (ScalarRangeExitPlan.scalar value)
  | none =>
    match extractScalarRangeExitWith locals slot source with
    | some plan => some plan
    | none =>
      match extractScalarBooleanWordRangeWith locals slot source with
      | some plan => some plan
      | none =>
        match source with
        | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type) condition) evidence) yes) no =>
            match scalarResultType? type with
            | none => none
            | some _ => do
                let guard ← extractScalarExprWith locals (BooleanRange.decision condition evidence)
                let first ← extractScalarWordRangeWith locals slot yes
                let second ← extractScalarWordRangeWith locals slot no
                pure (ScalarRangeExitPlan.choice guard first second)
        | .app (.app (.const ``Id.run [.zero]) type) body =>
            match scalarResultType? type with
            | none => none
            | some _ => extractScalarWordRangeWith locals slot body
        | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
            (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
              (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
                (.const ``Id.instMonad [.zero])))) type) body =>
            match scalarResultType? type with
            | none => none
            | some _ => extractScalarWordRangeWith locals slot body
        | .mdata _ body => extractScalarWordRangeWith locals slot body
        | _ => none
termination_by sizeOf source
decreasing_by all_goals simp_wf; omega

/-- Every supported word computation has an emitted scalar or loop plan. -/
theorem extractScalarWordRangeWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : WordRange.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarWordRangeWith locals slot source = some plan := by
  induction supported with
  | scalar body =>
    obtain ⟨value, accepted⟩ := extractScalarExprWith_accepts body locals typed total
    exact ⟨ScalarRangeExitPlan.scalar value, by rw [extractScalarWordRangeWith.eq_def, accepted]⟩
  | rangeExit body =>
    obtain ⟨plan, accepted⟩ := extractScalarRangeExitWith_accepts body locals slot typed total
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · rw [accepted]
      exact ⟨plan, rfl⟩
  | booleanWord body =>
    obtain ⟨plan, accepted⟩ := extractScalarBooleanWordRangeWith_accepts body locals slot typed total
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · rw [accepted]
        exact ⟨plan, rfl⟩
  | choice type condition _ _ yesIH noIH =>
    obtain ⟨guard, hg⟩ := extractScalarExprWith_accepts condition locals typed total
    obtain ⟨yes, hy⟩ := yesIH
    obtain ⟨no, hn⟩ := noIH
    simp only [WordRange.choiceExpr]
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp [scalarResultType_accepts, hg, hy, hn]
  | run type _ ih =>
    obtain ⟨plan, hp⟩ := ih
    simp only [Identity.run]
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp [scalarResultType_accepts, hp]
  | pure type _ ih =>
    obtain ⟨plan, hp⟩ := ih
    simp only [Identity.pure]
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp [scalarResultType_accepts, hp]
  | metadata _ ih =>
    obtain ⟨plan, hp⟩ := ih
    rw [extractScalarWordRangeWith.eq_def]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · exact ⟨plan, hp⟩

theorem extractScalarWordRangeWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarWordRangeWith locals slot source = some plan) :
    WordRange.Supported (locals.map ScalarBinding.kind) source := by
  fun_induction extractScalarWordRangeWith locals slot source generalizing plan with
  | case1 source value matched => exact .scalar (extractScalarExprWith_supported matched)
  | case2 source notScalar before matched => exact .rangeExit (extractScalarRangeExitWith_supported matched)
  | case3 source notScalar notRange before matched => exact .booleanWord (extractScalarBooleanWordRangeWith_supported matched)
  | case4 => contradiction
  | case5 type condition evidence yes no result parsed notScalar notRange notBoolean yesIH noIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨guard, hg, first, hy, second, hn, rfl⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .choice result (extractScalarExprWith_supported hg) (yesIH hy) (noIH hn)
  | case6 => contradiction
  | case7 type body result parsed notScalar notRange notBoolean ih =>
    rw [scalarResultType_sound parsed]
    exact .run result (ih compiled)
  | case8 => contradiction
  | case9 type body result parsed notScalar notRange notBoolean ih =>
    rw [scalarResultType_sound parsed]
    exact .pure result (ih compiled)
  | case10 data body notScalar notRange notBoolean ih => exact .metadata (ih compiled)
  | case11 => contradiction

/-- The selected word computation preserves its native source result. -/
theorem extractScalarWordRangeWith_correct {source : Lean.Expr} {locals : List ScalarBinding}
    {plan : ScalarRangeExitPlan} (saved : List UInt64) (values : List Value)
    (compiled : extractScalarWordRangeWith locals saved.length source = some plan)
    (typed : values.map Value.kind = locals.map ScalarBinding.kind)
    (bindings : RangeExitBindingsMatch locals values saved)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ value, WordRange.Eval source values value ∧ plan.Meaning saved value := by
  fun_induction extractScalarWordRangeWith locals saved.length source generalizing plan with
  | case1 source target matched =>
    cases compiled
    obtain ⟨value, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    exact ⟨value, .scalar evaluated, ScalarRangeExitPlan.scalar_meaning (fun accumulator index stop done =>
      extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))⟩
  | case2 source notScalar before matched =>
    cases compiled
    obtain ⟨value, evaluated, meaning⟩ := extractScalarRangeExitWith_correct saved values matched typed bindings total
    exact ⟨value, .rangeExit evaluated, meaning⟩
  | case3 source notScalar notRange before matched =>
    cases compiled
    obtain ⟨value, evaluated, meaning⟩ := extractScalarBooleanWordRangeWith_correct saved values matched typed bindings total
    exact ⟨value, .booleanWord evaluated, meaning⟩
  | case4 => contradiction
  | case5 type condition evidence yes no result parsed notScalar notRange notBoolean yesIH noIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨guard, hg, first, hy, second, hn, rfl⟩ := compiled
    rw [scalarResultType_sound parsed]
    obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported hg).evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    have stable : ∀ accumulator index stop done,
        guard.ScalarEval (LeanExe.IR.rangeExitStore saved accumulator index stop done) flag.toUInt64
          (LeanExe.IR.rangeExitStore saved accumulator index stop done) := by
      intro accumulator index stop done
      exact extractScalarExprWith_correct evaluated hg (bindings accumulator index stop done)
    cases flag with
    | false =>
      obtain ⟨value, branch, meaning⟩ := noIH hn
      exact ⟨value, .choice result evaluated branch, ScalarRangeExitPlan.choice_meaning stable meaning⟩
    | true =>
      obtain ⟨value, branch, meaning⟩ := yesIH hy
      exact ⟨value, .choice result evaluated branch, ScalarRangeExitPlan.choice_meaning stable meaning⟩
  | case6 => contradiction
  | case7 type body result parsed notScalar notRange notBoolean ih =>
    rw [scalarResultType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih compiled
    exact ⟨value, .run result evaluated, meaning⟩
  | case8 => contradiction
  | case9 type body result parsed notScalar notRange notBoolean ih =>
    rw [scalarResultType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih compiled
    exact ⟨value, .pure result evaluated, meaning⟩
  | case10 data body notScalar notRange notBoolean ih =>
    obtain ⟨value, evaluated, meaning⟩ := ih compiled
    exact ⟨value, .metadata evaluated, meaning⟩
  | case11 => contradiction

theorem extractScalarWordRangeWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {slot : Nat} (accumulator : P (.local slot)) (index : P (.local (slot + 1)))
    {source : Lean.Expr} {locals : List ScalarBinding} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarWordRangeWith locals slot source = some plan)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : plan.Holds P := by
  fun_induction extractScalarWordRangeWith locals slot source generalizing plan with
  | case1 source target matched =>
    cases compiled
    exact ScalarRangeExitPlan.scalar_holds P literal
      (extractScalarExprWith_invariant P literal binary choice matched bindings)
  | case2 source notScalar before matched =>
    cases compiled
    exact extractScalarRangeExitWith_invariant P literal binary choice accumulator index matched bindings
  | case3 source notScalar notRange before matched =>
    cases compiled
    exact extractScalarBooleanWordRangeWith_invariant P literal binary choice accumulator index matched bindings
  | case4 => contradiction
  | case5 type condition evidence yes no result parsed notScalar notRange notBoolean yesIH noIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨guard, hg, first, hy, second, hn, rfl⟩ := compiled
    exact ScalarRangeExitPlan.choice_holds P literal choice
      (extractScalarExprWith_invariant P literal binary choice hg bindings) (yesIH hy) (noIH hn)
  | case6 => contradiction
  | case7 type body result parsed notScalar notRange notBoolean ih => exact ih compiled
  | case8 => contradiction
  | case9 type body result parsed notScalar notRange notBoolean ih => exact ih compiled
  | case10 data body notScalar notRange notBoolean ih => exact ih compiled
  | case11 => contradiction

end LeanExe.Extract.Core
