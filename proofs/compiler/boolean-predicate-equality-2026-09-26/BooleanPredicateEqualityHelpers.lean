import LeanExe.Extract.ScalarBooleanPredicateJunction

namespace LeanExe.Source.Scalar

inductive BooleanEqualityForm where
  | equality
  | decision

def BooleanEqualityForm.local (form : BooleanEqualityForm) (n : Nat) (unequal : Bool)
    (left right : BooleanLocal) : BooleanLocal :=
  match form with
  | .equality => .equality n unequal left right
  | .decision => .relationDecision n unequal left right

def BooleanEqualityForm.denote (form : BooleanEqualityForm) (unequal left right : Bool) : Bool :=
  match form with
  | .equality => if unequal then left != right else left == right
  | .decision => booleanRelationDecision unequal left right

@[simp] theorem BooleanEqualityForm.denote_eq (form : BooleanEqualityForm) (unequal left right : Bool) :
    form.denote unequal left right = (if unequal then left != right else left == right) := by
  cases form <;> simp [denote]

@[simp] theorem BooleanEqualityForm.local_functions (form : BooleanEqualityForm) (n : Nat)
    (unequal : Bool) (left right : BooleanLocal) :
    (form.local n unequal left right).functions = left.functions ++ right.functions := by
  cases form <;> rfl

theorem BooleanEqualityForm.children_size (form : BooleanEqualityForm) (n : Nat)
    (unequal : Bool) (left right : BooleanLocal) :
    sizeOf left.expr < sizeOf (form.local n unequal left right).expr ∧
      sizeOf right.expr < sizeOf (form.local n unequal left right).expr := by
  cases form with
  | equality =>
    have bound := BooleanGuardNegation.expr_size n (booleanEqualityExpr unequal left.expr right.expr)
    cases unequal <;> simp [BooleanEqualityForm.local, BooleanLocal.expr, booleanEqualityExpr] at bound ⊢ <;> omega
  | decision =>
    have bound := BooleanGuardNegation.expr_size n (booleanRelationDecisionExpr unequal left.expr right.expr)
    cases unequal <;> simp [BooleanEqualityForm.local, BooleanLocal.expr, booleanRelationDecisionExpr,
      booleanRelationCondition, booleanRelationEvidence] at bound ⊢ <;> omega

end LeanExe.Source.Scalar

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
