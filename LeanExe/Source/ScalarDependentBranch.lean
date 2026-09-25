import LeanExe.Source.ScalarGuard

namespace LeanExe.Source.Scalar

/-- Exact dependent conditional syntax. Branch bodies keep the proof binder's
position even though that binder carries no executable word. -/
def Guard.dependentBranch (guard : Guard) (type : Lean.Expr)
    (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo)
    (onTrue onFalse : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) type)
    guard.condition) guard.evidence)
      (.lam trueName guard.condition onTrue trueBi))
      (.lam falseName (.app (.const ``Not []) guard.condition) onFalse falseBi)

end LeanExe.Source.Scalar
