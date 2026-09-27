import LeanExe.Extract.ScalarRangeExit

namespace LeanExe.Extract.Core

/-- Compose a scalar binding with a loop, or a loop binding with a scalar result. -/
def scalarRangeValueBinding (value : Option LeanExe.IR.Expr)
    (body : LeanExe.IR.Expr → Option ScalarRangeExitPlan)
    (loop : Unit → Option ScalarRangeExitPlan)
    (result : LeanExe.IR.Expr → Option LeanExe.IR.Expr) : Option ScalarRangeExitPlan :=
  (do let flag ← value; body flag).orElse fun _ => do
    let plan ← loop ()
    let tail ← result plan.result
    pure { plan with result := tail }

theorem scalarRangeValueBinding_accepts_primary {value : Option LeanExe.IR.Expr}
    {body : LeanExe.IR.Expr → Option ScalarRangeExitPlan} {loop : Unit → Option ScalarRangeExitPlan}
    {result : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {flag : LeanExe.IR.Expr} {plan : ScalarRangeExitPlan}
    (matched : value = some flag) (compiled : body flag = some plan) :
    scalarRangeValueBinding value body loop result = some plan := by
  simp [scalarRangeValueBinding, matched, compiled]

theorem scalarRangeValueBinding_accepts_loop {value : Option LeanExe.IR.Expr}
    {body : LeanExe.IR.Expr → Option ScalarRangeExitPlan} {loop : Unit → Option ScalarRangeExitPlan}
    {result : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {before : ScalarRangeExitPlan} {tail : LeanExe.IR.Expr}
    (compiled : loop () = some before) (matched : result before.result = some tail) :
    ∃ plan, scalarRangeValueBinding value body loop result = some plan := by
  cases first : (do let flag ← value; body flag) with
  | some plan => exact ⟨plan, by simp [scalarRangeValueBinding, first]⟩
  | none => exact ⟨{ before with result := tail }, by simp [scalarRangeValueBinding, first, compiled, matched]⟩

theorem scalarRangeValueBinding_success {value : Option LeanExe.IR.Expr}
    {body : LeanExe.IR.Expr → Option ScalarRangeExitPlan} {loop : Unit → Option ScalarRangeExitPlan}
    {result : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {plan : ScalarRangeExitPlan}
    (compiled : scalarRangeValueBinding value body loop result = some plan) :
    (∃ flag, value = some flag ∧ body flag = some plan) ∨
    (∃ before tail, loop () = some before ∧ result before.result = some tail ∧ plan = { before with result := tail }) := by
  unfold scalarRangeValueBinding at compiled
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


/-- Preserve an existing loop-result candidate before trying scalar setup. -/
def scalarRangeLoopFirstBinding (loop : Unit → Option ScalarRangeExitPlan)
    (result : LeanExe.IR.Expr → Option LeanExe.IR.Expr)
    (value : Unit → Option LeanExe.IR.Expr)
    (body : LeanExe.IR.Expr → Option ScalarRangeExitPlan) : Option ScalarRangeExitPlan :=
  (do let plan ← loop (); let tail ← result plan.result; pure { plan with result := tail }).orElse fun _ => do
    let bound ← value ()
    body bound

theorem scalarRangeLoopFirstBinding_accepts_loop {loop : Unit → Option ScalarRangeExitPlan}
    {result : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {value : Unit → Option LeanExe.IR.Expr}
    {body : LeanExe.IR.Expr → Option ScalarRangeExitPlan} {before : ScalarRangeExitPlan} {tail : LeanExe.IR.Expr}
    (compiled : loop () = some before) (matched : result before.result = some tail) :
    scalarRangeLoopFirstBinding loop result value body = some {before with result := tail} := by
  simp [scalarRangeLoopFirstBinding, compiled, matched]

theorem scalarRangeLoopFirstBinding_accepts_scalar {loop : Unit → Option ScalarRangeExitPlan}
    {result : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {value : Unit → Option LeanExe.IR.Expr}
    {body : LeanExe.IR.Expr → Option ScalarRangeExitPlan} {bound : LeanExe.IR.Expr} {plan : ScalarRangeExitPlan}
    (matched : value () = some bound) (compiled : body bound = some plan) :
    ∃ plan, scalarRangeLoopFirstBinding loop result value body = some plan := by
  cases first : (do let before ← loop (); let tail ← result before.result; pure {before with result := tail}) with
  | some target => exact ⟨target, by unfold scalarRangeLoopFirstBinding; rw [first]; rfl⟩
  | none => exact ⟨plan, by unfold scalarRangeLoopFirstBinding; rw [first]; simp [matched, compiled]⟩

theorem scalarRangeLoopFirstBinding_success {loop : Unit → Option ScalarRangeExitPlan}
    {result : LeanExe.IR.Expr → Option LeanExe.IR.Expr} {value : Unit → Option LeanExe.IR.Expr}
    {body : LeanExe.IR.Expr → Option ScalarRangeExitPlan} {plan : ScalarRangeExitPlan}
    (compiled : scalarRangeLoopFirstBinding loop result value body = some plan) :
    (∃ before tail, loop () = some before ∧ result before.result = some tail ∧ plan = {before with result := tail}) ∨
    (∃ bound, value () = some bound ∧ body bound = some plan) := by
  unfold scalarRangeLoopFirstBinding at compiled
  cases first : (do let before ← loop (); let tail ← result before.result; pure {before with result := tail}) with
  | some target =>
    have same : target = plan := by rw [first] at compiled; simpa only [Option.orElse, Option.some.injEq] using compiled
    subst target
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at first
    obtain ⟨before, hp, tail, hr, same⟩ := first
    exact .inl ⟨before, tail, hp, hr, same.symm⟩
  | none =>
    have second : (do let bound ← value (); body bound) = some plan := by rw [first] at compiled; simpa only [Option.orElse, Option.some.injEq] using compiled
    exact .inr (by simpa only [bind, Option.bind_eq_some_iff] using second)

end LeanExe.Extract.Core
