import LeanExe.Source.ScalarBooleanChoiceForm

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

