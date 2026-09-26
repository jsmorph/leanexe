import LeanExe.Source.ScalarBooleanConditionInputs
import LeanExe.Extract.ScalarBooleanPredicateChoice

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def extractBooleanCondition {value : BooleanLocal} (form : BooleanConditionForm value)
    (extract : (input : BooleanLocal) → input ∈ form.inputs → Option LeanExe.IR.Expr) :
    Option LeanExe.IR.Cond :=
  match form with
  | .truth value => do
      let result ← extract value (by simp [BooleanConditionForm.inputs])
      pure (wordGuard result)
  | .equal left right _ => do
      let first ← extract left (by simp [BooleanConditionForm.inputs])
      let second ← extract right (by simp [BooleanConditionForm.inputs])
      pure (lowerComparison .beq first second)
  | .unequal left right => do
      let first ← extract left (by simp [BooleanConditionForm.inputs])
      let second ← extract right (by simp [BooleanConditionForm.inputs])
      pure (lowerComparison .bne first second)

theorem extractBooleanCondition_accepts {value : BooleanLocal} (form : BooleanConditionForm value)
    (extract : (input : BooleanLocal) → input ∈ form.inputs → Option LeanExe.IR.Expr)
    (arguments : ∀ input member, ∃ result, extract input member = some result) :
    ∃ result, extractBooleanCondition form extract = some result := by
  cases form with
  | truth value =>
    obtain ⟨result, found⟩ := arguments value (by simp [BooleanConditionForm.inputs])
    exact ⟨wordGuard result, by simp [extractBooleanCondition, found]⟩
  | equal left right nontrue =>
    obtain ⟨first, hl⟩ := arguments left (by simp [BooleanConditionForm.inputs])
    obtain ⟨second, hr⟩ := arguments right (by simp [BooleanConditionForm.inputs])
    exact ⟨lowerComparison .beq first second, by simp [extractBooleanCondition, hl, hr]⟩
  | unequal left right =>
    obtain ⟨first, hl⟩ := arguments left (by simp [BooleanConditionForm.inputs])
    obtain ⟨second, hr⟩ := arguments right (by simp [BooleanConditionForm.inputs])
    exact ⟨lowerComparison .bne first second, by simp [extractBooleanCondition, hl, hr]⟩

theorem extractBooleanCondition_inputs {value : BooleanLocal} (form : BooleanConditionForm value)
    (extract : (input : BooleanLocal) → input ∈ form.inputs → Option LeanExe.IR.Expr)
    {result : LeanExe.IR.Cond} (compiled : extractBooleanCondition form extract = some result)
    (input : BooleanLocal) (member : input ∈ form.inputs) :
    ∃ expression, extract input member = some expression := by
  cases form with
  | truth value =>
    simp only [extractBooleanCondition, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨expression, found, _⟩ := compiled
    simp only [BooleanConditionForm.inputs, List.mem_singleton] at member
    subst input
    exact ⟨expression, found⟩
  | equal left right nontrue =>
    simp only [extractBooleanCondition, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, _⟩ := compiled
    simp only [BooleanConditionForm.inputs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨first, hl⟩
    · exact ⟨second, hr⟩
  | unequal left right =>
    simp only [extractBooleanCondition, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, _⟩ := compiled
    simp only [BooleanConditionForm.inputs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨first, hl⟩
    · exact ⟨second, hr⟩

theorem extractBooleanCondition_correct {value : BooleanLocal} (form : BooleanConditionForm value)
    (extract : (input : BooleanLocal) → input ∈ form.inputs → Option LeanExe.IR.Expr)
    (native : BooleanLocal → Bool) {result : LeanExe.IR.Cond} {store : LeanExe.IR.ScalarStore}
    (compiled : extractBooleanCondition form extract = some result)
    (arguments : ∀ input member expression, extract input member = some expression →
      expression.ScalarEval store (native input).toUInt64 store) :
    result.ScalarEval store (form.denoteInputs native) store := by
  cases form with
  | truth value =>
    simp only [extractBooleanCondition, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨expression, found, rfl⟩ := compiled
    exact wordGuard_correct (arguments value _ expression found)
  | equal left right nontrue =>
    simp only [extractBooleanCondition, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, rfl⟩ := compiled
    have firstEval := arguments left _ first hl
    have secondEval := arguments right _ second hr
    cases ha : native left <;> cases hb : native right <;>
      simp only [BooleanConditionForm.denoteInputs, ha, hb] at firstEval secondEval ⊢
    all_goals exact lowerComparison_correct _ firstEval secondEval
  | unequal left right =>
    simp only [extractBooleanCondition, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, rfl⟩ := compiled
    have firstEval := arguments left _ first hl
    have secondEval := arguments right _ second hr
    cases ha : native left <;> cases hb : native right <;>
      simp only [BooleanConditionForm.denoteInputs, ha, hb] at firstEval secondEval ⊢
    all_goals exact lowerComparison_correct _ firstEval secondEval

theorem extractBooleanCondition_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {value : BooleanLocal} (form : BooleanConditionForm value)
    (extract : (input : BooleanLocal) → input ∈ form.inputs → Option LeanExe.IR.Expr)
    {result : LeanExe.IR.Cond} (compiled : extractBooleanCondition form extract = some result)
    (arguments : ∀ input member expression, extract input member = some expression → P expression)
    (yes no : LeanExe.IR.Expr) (ht : P yes) (he : P no) : P (.ite result yes no) := by
  cases form with
  | truth value =>
    simp only [extractBooleanCondition, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨expression, found, rfl⟩ := compiled
    exact choice .eq _ _ _ _ (arguments value _ expression found) (literal 1) ht he
  | equal left right nontrue =>
    simp only [extractBooleanCondition, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, rfl⟩ := compiled
    exact choice .beq _ _ _ _ (arguments left _ first hl) (arguments right _ second hr) ht he
  | unequal left right =>
    simp only [extractBooleanCondition, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hl, second, hr, rfl⟩ := compiled
    exact choice .bne _ _ _ _ (arguments left _ first hl) (arguments right _ second hr) ht he

theorem scalarConditional_correct {condition : LeanExe.IR.Cond}
    {yes no : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore} {flag : Bool} {value : UInt64}
    (test : condition.ScalarEval store flag store)
    (branch : (if flag then yes else no).ScalarEval store value store) :
    (LeanExe.IR.Expr.ite condition yes no).ScalarEval store value store := by
  cases flag with
  | false => exact .iteFalse test branch
  | true => exact .iteTrue test branch

end LeanExe.Extract.Core
