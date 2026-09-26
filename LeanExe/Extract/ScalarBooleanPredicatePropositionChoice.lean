import LeanExe.Source.ScalarBooleanPropositionChoiceForm
import LeanExe.Extract.ScalarBooleanPredicateChoice

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def booleanWordConditional (n : Nat) (condition : LeanExe.IR.Cond) (yes no : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  booleanWordNegation n (.ite condition yes no)

theorem booleanWordConditional_correct (n : Nat)
    {condition : LeanExe.IR.Cond} {yes no : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore}
    {flag value : Bool} (test : condition.ScalarEval store flag store)
    (branch : (if flag then yes else no).ScalarEval store value.toUInt64 store) :
    (booleanWordConditional n condition yes no).ScalarEval store
      (GuardNegation.denote n value).toUInt64 store := by
  apply booleanWordNegation_correct
  cases flag with
  | false => exact .iteFalse test branch
  | true => exact .iteTrue test branch

theorem booleanWordConditional_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (n : Nat) {condition : LeanExe.IR.Cond} {yes no : LeanExe.IR.Expr}
    (guard : ∀ t e, P t → P e → P (.ite condition t e))
    (trueBranch : P yes) (falseBranch : P no) :
    P (booleanWordConditional n condition yes no) :=
  booleanWordNegation_holds P literal choice n (guard _ _ trueBranch falseBranch)

end LeanExe.Extract.Core
