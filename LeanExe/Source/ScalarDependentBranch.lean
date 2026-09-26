import LeanExe.Source.ScalarDecidedGuard

namespace LeanExe.Source.Scalar

/-- Exact dependent conditional syntax. Branch bodies keep the proof binder's
position even though that binder carries no executable word. -/
def DecidedGuard.dependentBranch (guard : DecidedGuard) (type : Lean.Expr)
    (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo)
    (onTrue onFalse : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) type)
    guard.condition) guard.evidence)
      (.lam trueName guard.condition onTrue trueBi))
      (.lam falseName (.app (.const ``Not []) guard.condition) onFalse falseBi)

/-- Canonical dependent guards retain the original syntax helper. -/
abbrev Guard.dependentBranch (guard : Guard) (type : Lean.Expr)
    (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo)
    (onTrue onFalse : Lean.Expr) : Lean.Expr :=
  (DecidedGuard.canonical guard).dependentBranch type trueName falseName trueBi falseBi onTrue onFalse

end LeanExe.Source.Scalar
