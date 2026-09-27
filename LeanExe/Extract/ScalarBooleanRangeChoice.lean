import LeanExe.Extract.ScalarBooleanRange
import LeanExe.Extract.ScalarRangeExitCorrectness
import LeanExe.Extract.ScalarRangeExitInvariant

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar
open LeanExe.IR (rangeExitStore)

theorem ScalarRangeExitPlan.scalar_meaning {target : LeanExe.IR.Expr}
    {saved : List UInt64} {value : UInt64}
    (stable : ∀ accumulator index stop done,
      target.ScalarEval (rangeExitStore saved accumulator index stop done) value
        (rangeExitStore saved accumulator index stop done)) :
    (ScalarRangeExitPlan.scalar target).Meaning saved value := by
  refine ⟨0, 0, (fun _ a => ForInStep.yield a), .const, .const, ?_, ?_⟩
  · intro index bound
    have impossible : index < 0 := bound
    omega
  · intro done
    exact stable 0 0 0 done

theorem ScalarRangeExitPlan.scalar_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n)) {value : LeanExe.IR.Expr} (holds : P value) :
    (ScalarRangeExitPlan.scalar value).Holds P :=
  ⟨literal 0, literal 0, literal 0, literal 0, holds⟩

theorem scalarBooleanRangeArm_correct {locals : List ScalarBinding} {source : Lean.Expr}
    {plan : ScalarRangeExitPlan} (saved : List UInt64) (values : List Value)
    (compiled : scalarBooleanRangeArm (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) source))
      (fun _ => extractScalarBooleanRangeWith locals saved.length source) = some plan)
    (typed : values.map Value.kind = locals.map ScalarBinding.kind)
    (bindings : RangeExitBindingsMatch locals values saved)
    (fallback : ∀ plan, extractScalarBooleanRangeWith locals saved.length source = some plan →
      ∃ flag, BooleanRange.Eval source values flag ∧ plan.Meaning saved flag.toUInt64) :
    ∃ flag, (EvalWith (.app (.const ``Bool.toUInt64 []) source) values flag.toUInt64 ∨
      BooleanRange.Eval source values flag) ∧ plan.Meaning saved flag.toUInt64 := by
  rcases scalarBooleanRangeArm_success compiled with ⟨value, matched, rfl⟩ | ⟨notScalar, matched⟩
  · obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨flag, .inl evaluated, ScalarRangeExitPlan.scalar_meaning (fun accumulator index stop done =>
      extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))⟩
  · obtain ⟨flag, evaluated, meaning⟩ := fallback plan matched
    exact ⟨flag, .inr evaluated, meaning⟩

theorem scalarBooleanRangeArm_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {locals : List ScalarBinding} {source : Lean.Expr} {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : scalarBooleanRangeArm (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) source))
      (fun _ => extractScalarBooleanRangeWith locals slot source) = some plan)
    (bindings : ∀ binding ∈ locals, binding.Holds P)
    (fallback : ∀ plan, extractScalarBooleanRangeWith locals slot source = some plan → plan.Holds P) :
    plan.Holds P := by
  rcases scalarBooleanRangeArm_success compiled with ⟨value, matched, rfl⟩ | ⟨notScalar, matched⟩
  · exact ScalarRangeExitPlan.scalar_holds P literal
      (extractScalarExprWith_invariant P literal binary choice matched bindings)
  · exact fallback plan matched

/-- A captured condition selects the same branch at every loop state. -/
theorem ScalarRangeExitPlan.choice_meaning {guard : LeanExe.IR.Expr}
    {yes no : ScalarRangeExitPlan} {saved : List UInt64} {flag : Bool} {value : UInt64}
    (condition : ∀ accumulator index stop done,
      guard.ScalarEval (rangeExitStore saved accumulator index stop done) flag.toUInt64
        (rangeExitStore saved accumulator index stop done))
    (selected : (if flag then yes else no).Meaning saved value) :
    (ScalarRangeExitPlan.choice guard yes no).Meaning saved value := by
  have decision (accumulator index stop done) :
      (lowerComparison .bne guard (.u64 0)).ScalarEval
        (rangeExitStore saved accumulator index stop done) flag
        (rangeExitStore saved accumulator index stop done) := by
    cases flag <;> exact lowerComparison_correct .bne (condition accumulator index stop done) .const
  cases flag with
  | false =>
    obtain ⟨stop, start, step, countEval, initialEval, stepEval, resultEval⟩ := selected
    refine ⟨stop, start, step, .iteFalse (decision 0 0 0 0) countEval,
      .iteFalse (decision 0 0 stop 0) initialEval, ?_, ?_⟩
    · intro index bound accumulator done
      obtain ⟨advanced, exited⟩ := stepEval index bound accumulator done
      exact ⟨.iteFalse (decision accumulator index stop done) advanced,
        .iteFalse (decision accumulator index stop done) exited⟩
    · intro done
      exact .iteFalse (decision _ _ _ done) (resultEval done)
  | true =>
    obtain ⟨stop, start, step, countEval, initialEval, stepEval, resultEval⟩ := selected
    refine ⟨stop, start, step, .iteTrue (decision 0 0 0 0) countEval,
      .iteTrue (decision 0 0 stop 0) initialEval, ?_, ?_⟩
    · intro index bound accumulator done
      obtain ⟨advanced, exited⟩ := stepEval index bound accumulator done
      exact ⟨.iteTrue (decision accumulator index stop done) advanced,
        .iteTrue (decision accumulator index stop done) exited⟩
    · intro done
      exact .iteTrue (decision _ _ _ done) (resultEval done)

theorem ScalarRangeExitPlan.choice_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {guard : LeanExe.IR.Expr} {yes no : ScalarRangeExitPlan}
    (condition : P guard) (first : yes.Holds P) (second : no.Holds P) :
    (ScalarRangeExitPlan.choice guard yes no).Holds P := by
  obtain ⟨yc, yi, ys, yd, yr⟩ := first
  obtain ⟨nc, ni, ns, nd, nr⟩ := second
  exact ⟨choice .bne guard (.u64 0) _ _ condition (literal 0) yc nc,
    choice .bne guard (.u64 0) _ _ condition (literal 0) yi ni,
    choice .bne guard (.u64 0) _ _ condition (literal 0) ys ns,
    choice .bne guard (.u64 0) _ _ condition (literal 0) yd nd,
    choice .bne guard (.u64 0) _ _ condition (literal 0) yr nr⟩

end LeanExe.Extract.Core
