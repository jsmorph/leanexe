import LeanExe.Extract.ScalarGuardLowering

namespace LeanExe.Extract.Core

/-- Preserve the ordinary Boolean condition when equality tests the literal true.
Other Boolean relations compare both checked zero/one values. -/
def lowerBooleanChoiceCondition (unequal literalTrue : Bool) (left right : LeanExe.IR.Cond) : LeanExe.IR.Cond :=
  if !unequal && literalTrue then left else lowerBooleanEquality unequal left right

theorem lowerBooleanChoiceCondition_correct (unequal literalTrue : Bool) {left right : LeanExe.IR.Cond}
    {store : LeanExe.IR.ScalarStore} {a b : Bool}
    (first : left.ScalarEval store a store) (second : right.ScalarEval store b store)
    (literalMeaning : literalTrue = true → b = true) :
    (lowerBooleanChoiceCondition unequal literalTrue left right).ScalarEval store
      (if unequal then a != b else a == b) store := by
  unfold lowerBooleanChoiceCondition
  split
  · rename_i direct
    have both : unequal = false ∧ literalTrue = true := by
      cases unequal <;> cases literalTrue <;> simp_all
    obtain ⟨equal, literal⟩ := both
    have truth := literalMeaning literal
    subst unequal
    subst b
    cases a <;> exact first
  · exact lowerBooleanEquality_correct unequal first second

theorem lowerBooleanChoiceCondition_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (unequal literalTrue : Bool) (left right : LeanExe.IR.Cond)
    (first : ∀ t e, P t → P e → P (.ite left t e))
    (second : ∀ t e, P t → P e → P (.ite right t e)) :
    ∀ t e, P t → P e → P (.ite (lowerBooleanChoiceCondition unequal literalTrue left right) t e) := by
  unfold lowerBooleanChoiceCondition
  split
  · exact first
  · exact lowerBooleanEquality_choice P literal choice unequal left right first second

end LeanExe.Extract.Core
