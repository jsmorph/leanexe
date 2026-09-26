import LeanExe.Extract.ScalarBooleanPredicateEquality

namespace LeanExe.Source.Scalar

inductive BooleanChoiceForm where
  | ordinary
  | dependent (shape : BooleanProofBranch)

def BooleanChoiceForm.local (form : BooleanChoiceForm) (n : Nat) (unequal : Bool)
    (left right yes no : BooleanLocal) : BooleanLocal :=
  match form with
  | .ordinary => .choice n unequal left right yes no
  | .dependent shape => .dependentChoice n shape unequal left right yes no

@[simp] theorem BooleanChoiceForm.local_functions (form : BooleanChoiceForm) (n : Nat)
    (unequal : Bool) (left right yes no : BooleanLocal) :
    (form.local n unequal left right yes no).functions =
      left.functions ++ (right.functions ++ (yes.functions ++ no.functions)) := by
  cases form <;> rfl

theorem BooleanChoiceForm.children_size (form : BooleanChoiceForm) (n : Nat)
    (unequal : Bool) (left right yes no : BooleanLocal) :
    sizeOf left.expr < sizeOf (form.local n unequal left right yes no).expr ∧
    sizeOf right.expr < sizeOf (form.local n unequal left right yes no).expr ∧
    sizeOf yes.expr < sizeOf (form.local n unequal left right yes no).expr ∧
    sizeOf no.expr < sizeOf (form.local n unequal left right yes no).expr := by
  cases form with
  | ordinary =>
    have bound := BooleanGuardNegation.expr_size n
      (booleanChoiceExpr unequal left.expr right.expr yes.expr no.expr)
    simp [BooleanChoiceForm.local, BooleanLocal.expr, booleanChoiceExpr,
      booleanRelationCondition] at bound ⊢
    omega
  | dependent shape =>
    have bound := BooleanGuardNegation.expr_size n
      (shape.expr (booleanRelationCondition unequal left.expr right.expr)
        (booleanRelationEvidence unequal left.expr right.expr) yes.expr no.expr)
    have operands := booleanRelationCondition_sizes unequal left.expr right.expr
    have condition := shape.condition_size (booleanRelationCondition unequal left.expr right.expr)
      (booleanRelationEvidence unequal left.expr right.expr) yes.expr no.expr
    have yesBound := shape.yes_size (booleanRelationCondition unequal left.expr right.expr)
      (booleanRelationEvidence unequal left.expr right.expr) yes.expr no.expr
    have noBound := shape.no_size (booleanRelationCondition unequal left.expr right.expr)
      (booleanRelationEvidence unequal left.expr right.expr) yes.expr no.expr
    simp only [BooleanChoiceForm.local, BooleanLocal.expr]
    omega

end LeanExe.Source.Scalar

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def booleanWordChoice (n : Nat) (unequal : Bool) (left right yes no : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  booleanWordNegation n (.ite (lowerComparison (if unequal then .bne else .beq) left right) yes no)

theorem booleanWordChoice_correct (n : Nat) (unequal : Bool)
    {left right yes no : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore} {a b value : Bool}
    (first : left.ScalarEval store a.toUInt64 store)
    (second : right.ScalarEval store b.toUInt64 store)
    (branch : (if booleanRelationDecision unequal a b then yes else no).ScalarEval store value.toUInt64 store) :
    (booleanWordChoice n unequal left right yes no).ScalarEval store
      (GuardNegation.denote n value).toUInt64 store := by
  have condition : (lowerComparison (if unequal then .bne else .beq) left right).ScalarEval
      store (booleanRelationDecision unequal a b) store := by
    cases unequal <;> cases a <;> cases b <;> exact lowerComparison_correct _ first second
  apply booleanWordNegation_correct
  cases result : booleanRelationDecision unequal a b with
  | false => exact .iteFalse (by simpa only [result] using condition) (by simpa only [result, Bool.false_eq_true, ↓reduceIte] using branch)
  | true => exact .iteTrue (by simpa only [result] using condition) (by simpa only [result, Bool.false_eq_true, ↓reduceIte] using branch)

theorem booleanWordChoice_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (n : Nat) (unequal : Bool) {left right yes no : LeanExe.IR.Expr}
    (first : P left) (second : P right) (trueBranch : P yes) (falseBranch : P no) :
    P (booleanWordChoice n unequal left right yes no) :=
  booleanWordNegation_holds P literal choice n
    (choice _ _ _ _ _ first second trueBranch falseBranch)

end LeanExe.Extract.Core
