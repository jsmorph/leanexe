import LeanExe.Source.ScalarBooleanEqualityForm
import LeanExe.Extract.ScalarBooleanPredicateJunction

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def booleanWordEquality (n : Nat) (unequal : Bool) (left right : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  booleanWordNegation n (guardWord (lowerComparison (if unequal then .bne else .beq) left right))

theorem booleanWordEquality_correct (form : BooleanEqualityForm) (n : Nat) (unequal : Bool)
    {left right : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore} {a b : Bool}
    (first : left.ScalarEval store a.toUInt64 store)
    (second : right.ScalarEval store b.toUInt64 store) :
    (booleanWordEquality n unequal left right).ScalarEval store
      (GuardNegation.denote n (form.denote unequal a b)).toUInt64 store := by
  rw [BooleanEqualityForm.denote_eq]
  apply booleanWordNegation_correct
  apply guardWord_correct
  cases unequal <;> cases a <;> cases b <;> exact lowerComparison_correct _ first second

theorem booleanWordEquality_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (n : Nat) (unequal : Bool) {left right : LeanExe.IR.Expr}
    (first : P left) (second : P right) : P (booleanWordEquality n unequal left right) :=
  booleanWordNegation_holds P literal choice n
    (choice _ _ _ _ _ first second (literal 1) (literal 0))

end LeanExe.Extract.Core
