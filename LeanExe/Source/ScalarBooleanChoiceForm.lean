import LeanExe.Source.ScalarBooleanLocal

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

