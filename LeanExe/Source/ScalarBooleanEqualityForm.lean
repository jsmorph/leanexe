import LeanExe.Source.ScalarBooleanLocal

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

