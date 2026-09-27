import LeanExe.Extract.ScalarBooleanRange
import LeanExe.Extract.ScalarRangeExitCorrectness
import LeanExe.Extract.ScalarRangeExitInvariant

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar
open LeanExe.IR (rangeExitStore)

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
