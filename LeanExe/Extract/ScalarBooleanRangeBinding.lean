import LeanExe.Extract.ScalarRangeExit

namespace LeanExe.Extract.Core

/-- Bind a scalar flag before a loop, or bind a loop's flag before a scalar result. -/
def scalarBooleanRangeFlagBinding (value : Option LeanExe.IR.Expr)
    (body : LeanExe.IR.Expr → Option ScalarRangeExitPlan)
    (loop : Unit → Option ScalarRangeExitPlan)
    (result : LeanExe.IR.Expr → Option LeanExe.IR.Expr) : Option ScalarRangeExitPlan :=
  (do let flag ← value; body flag).orElse fun _ => do
    let plan ← loop ()
    let tail ← result plan.result
    pure { plan with result := tail }

theorem scalarBooleanRangeFlagBinding_accepts_primary {value : Option LeanExe.IR.Expr}
    {body : LeanExe.IR.Expr → Option ScalarRangeExitPlan} {loop : Unit → Option ScalarRangeExitPlan}
    {result : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {flag : LeanExe.IR.Expr} {plan : ScalarRangeExitPlan}
    (matched : value = some flag) (compiled : body flag = some plan) :
    scalarBooleanRangeFlagBinding value body loop result = some plan := by
  simp [scalarBooleanRangeFlagBinding, matched, compiled]

theorem scalarBooleanRangeFlagBinding_accepts_loop {value : Option LeanExe.IR.Expr}
    {body : LeanExe.IR.Expr → Option ScalarRangeExitPlan} {loop : Unit → Option ScalarRangeExitPlan}
    {result : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {before : ScalarRangeExitPlan} {tail : LeanExe.IR.Expr}
    (compiled : loop () = some before) (matched : result before.result = some tail) :
    ∃ plan, scalarBooleanRangeFlagBinding value body loop result = some plan := by
  cases first : (do let flag ← value; body flag) with
  | some plan => exact ⟨plan, by simp [scalarBooleanRangeFlagBinding, first]⟩
  | none => exact ⟨{ before with result := tail }, by simp [scalarBooleanRangeFlagBinding, first, compiled, matched]⟩

theorem scalarBooleanRangeFlagBinding_success {value : Option LeanExe.IR.Expr}
    {body : LeanExe.IR.Expr → Option ScalarRangeExitPlan} {loop : Unit → Option ScalarRangeExitPlan}
    {result : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {plan : ScalarRangeExitPlan}
    (compiled : scalarBooleanRangeFlagBinding value body loop result = some plan) :
    (∃ flag, value = some flag ∧ body flag = some plan) ∨
    (∃ before tail, loop () = some before ∧ result before.result = some tail ∧ plan = { before with result := tail }) := by
  unfold scalarBooleanRangeFlagBinding at compiled
  cases first : (do let flag ← value; body flag) with
  | some target =>
    have same : target = plan := by simpa [first] using compiled
    subst target
    exact .inl (by simpa only [bind, Option.bind_eq_some_iff] using first)
  | none =>
    have second : (do let before ← loop (); let tail ← result before.result; pure { before with result := tail }) = some plan := by
      simpa [first] using compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at second
    obtain ⟨before, hp, tail, hr, same⟩ := second
    exact .inr ⟨before, tail, hp, hr, same.symm⟩

end LeanExe.Extract.Core
