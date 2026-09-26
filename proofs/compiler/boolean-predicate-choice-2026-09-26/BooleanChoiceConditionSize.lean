import LeanExe.Extract.ScalarBooleanPredicateEquality

open LeanExe.Source.Scalar

def small : BooleanLocal := .var 0 0
#eval sizeOf (BooleanLocal.choice 0 false small small small small).expr
#eval sizeOf (BooleanLocal.relationDecision 0 false small small).expr

theorem choiceCondition_size (n : Nat) (unequal : Bool) (left right yes no : BooleanLocal) :
    sizeOf (BooleanLocal.relationDecision 0 unequal left right).expr <
      sizeOf (BooleanLocal.choice n unequal left right yes no).expr := by
  have bound := BooleanGuardNegation.expr_size n
    (booleanChoiceExpr unequal left.expr right.expr yes.expr no.expr)
  simp [BooleanLocal.expr, BooleanGuardNegation.expr, booleanRelationDecisionExpr,
    booleanChoiceExpr] at bound ⊢
  omega

theorem propositionCondition_size (n : Nat) (guard : PropositionGuard) (yes no : BooleanLocal) :
    sizeOf (BooleanLocal.decision 0 guard).expr <
      sizeOf (BooleanLocal.proposition n guard yes no).expr := by
  have bound := BooleanGuardNegation.expr_size n (guard.branch yes.expr no.expr)
  simp [BooleanLocal.expr, BooleanGuardNegation.expr, DecidedGuard.decisionExpr,
    PropositionGuard.branch] at bound ⊢
  omega
