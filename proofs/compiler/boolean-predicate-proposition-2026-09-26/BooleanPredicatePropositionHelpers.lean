import LeanExe.Extract.ScalarBooleanPredicateChoice

namespace LeanExe.Source.Scalar

def BooleanChoiceForm.proposition (form : BooleanChoiceForm) (n : Nat)
    (guard : PropositionGuard) (yes no : BooleanLocal) : BooleanLocal :=
  match form with
  | .ordinary => .proposition n guard yes no
  | .dependent shape => .dependentProposition n shape guard yes no

@[simp] theorem BooleanChoiceForm.proposition_functions (form : BooleanChoiceForm) (n : Nat)
    (guard : PropositionGuard) (yes no : BooleanLocal) :
    (form.proposition n guard yes no).functions = yes.functions ++ no.functions := by
  cases form <;> rfl

theorem BooleanChoiceForm.proposition_children_size (form : BooleanChoiceForm) (n : Nat)
    (guard : PropositionGuard) (yes no : BooleanLocal) :
    sizeOf yes.expr < sizeOf (form.proposition n guard yes no).expr ∧
      sizeOf no.expr < sizeOf (form.proposition n guard yes no).expr := by
  cases form with
  | ordinary =>
    have bound := BooleanGuardNegation.expr_size n (guard.branch yes.expr no.expr)
    simp [BooleanChoiceForm.proposition, BooleanLocal.expr, PropositionGuard.branch] at bound ⊢
    omega
  | dependent shape =>
    have bound := BooleanGuardNegation.expr_size n (shape.expr guard.condition guard.evidence yes.expr no.expr)
    have yesBound := shape.yes_size guard.condition guard.evidence yes.expr no.expr
    have noBound := shape.no_size guard.condition guard.evidence yes.expr no.expr
    simp only [BooleanChoiceForm.proposition, BooleanLocal.expr]
    omega

theorem BooleanChoiceForm.proposition_operands_size (form : BooleanChoiceForm) (n : Nat)
    (guard : PropositionGuard) (yes no : BooleanLocal) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) :
    sizeOf operand < sizeOf (form.proposition n guard yes no).expr := by
  apply BooleanLocal.operands_size
  cases form <;> simp only [BooleanChoiceForm.proposition, BooleanLocal.operands]
  all_goals exact List.mem_append_left _ member

end LeanExe.Source.Scalar

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
