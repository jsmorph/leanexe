import LeanExe.Extract.ScalarGuardLowering

namespace LeanExe.Extract.Core

/-- Negate an encoded Boolean while preserving an unwrapped call's expression. -/
def booleanWordNegation (n : Nat) (value : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  match n with
  | 0 => value
  | n + 1 => guardWord (lowerGuardNegations (n + 1) (wordGuard value))

theorem booleanWordNegation_correct (n : Nat) {expression : LeanExe.IR.Expr}
    {store : LeanExe.IR.ScalarStore} {value : Bool}
    (evaluated : expression.ScalarEval store (Bool.toUInt64 value) store) :
    (booleanWordNegation n expression).ScalarEval store
      (Bool.toUInt64 (LeanExe.Source.Scalar.GuardNegation.denote n value)) store := by
  cases n with
  | zero => exact evaluated
  | succ n => exact guardWord_correct (lowerGuardNegations_correct (n + 1) (wordGuard_correct evaluated))

theorem booleanWordNegation_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (n : Nat) {expression : LeanExe.IR.Expr} (held : P expression) :
    P (booleanWordNegation n expression) := by
  cases n with
  | zero => exact held
  | succ n =>
    exact lowerGuardNegations_choice P literal choice (n + 1) _
      (fun t e ht he => choice .eq _ _ _ _ held (literal 1) ht he)
      _ _ (literal 1) (literal 0)

end LeanExe.Extract.Core
