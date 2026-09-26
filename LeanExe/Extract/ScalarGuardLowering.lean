import LeanExe.Source.ScalarGuard
import LeanExe.Extract.ScalarComparison
import LeanExe.Extract.ScalarPrimitive

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (Junction)

/-- A pure comparison result is materialized as the word zero or one. -/
def guardWord (condition : LeanExe.IR.Cond) : LeanExe.IR.Expr :=
  .ite condition (.u64 1) (.u64 0)

def wordGuard (value : LeanExe.IR.Expr) : LeanExe.IR.Cond := .eqU64 value (.u64 1)

/-- Choose a Boolean branch using the existing word conditional. -/
def lowerBooleanChoice (condition yes no : LeanExe.IR.Cond) : LeanExe.IR.Cond :=
  wordGuard (.ite condition (guardWord yes) (guardWord no))

/-- Compare the canonical zero/one words of two Boolean values. -/
def lowerBooleanEquality (unequal : Bool) (left right : LeanExe.IR.Cond) : LeanExe.IR.Cond :=
  lowerComparison (if unequal then .bne else .beq) (guardWord left) (guardWord right)

def junctionPrimitive : Junction → ScalarPrimitive
  | .conjunction => .land
  | .disjunction => .lor

def lowerJunction (op : Junction) (left right : LeanExe.IR.Cond) : LeanExe.IR.Cond :=
  wordGuard ((junctionPrimitive op).lower (guardWord left) (guardWord right))

theorem guardWord_correct {condition : LeanExe.IR.Cond} {store : LeanExe.IR.ScalarStore} {value : Bool}
    (evaluated : condition.ScalarEval store value store) :
    (guardWord condition).ScalarEval store (Bool.toUInt64 value) store := by
  cases value
  · exact .iteFalse evaluated .const
  · exact .iteTrue evaluated .const

theorem wordGuard_correct {expression : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore} {value : Bool}
    (evaluated : expression.ScalarEval store (Bool.toUInt64 value) store) :
    (wordGuard expression).ScalarEval store value store := by
  cases value
  · exact .eq evaluated .const
  · exact .eq evaluated .const

theorem lowerBooleanChoice_correct {condition yes no : LeanExe.IR.Cond}
    {store : LeanExe.IR.ScalarStore} {c t e : Bool}
    (test : condition.ScalarEval store c store)
    (first : yes.ScalarEval store t store) (second : no.ScalarEval store e store) :
    (lowerBooleanChoice condition yes no).ScalarEval store (if c then t else e) store := by
  apply wordGuard_correct
  cases c
  · exact .iteFalse test (guardWord_correct second)
  · exact .iteTrue test (guardWord_correct first)

theorem lowerBooleanChoice_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (condition yes no : LeanExe.IR.Cond)
    (test : ∀ t e, P t → P e → P (.ite condition t e))
    (first : ∀ t e, P t → P e → P (.ite yes t e))
    (second : ∀ t e, P t → P e → P (.ite no t e)) :
    ∀ t e, P t → P e → P (.ite (lowerBooleanChoice condition yes no) t e) := by
  intro t e ht he
  exact choice .eq _ _ _ _
    (test _ _ (first _ _ (literal 1) (literal 0)) (second _ _ (literal 1) (literal 0)))
    (literal 1) ht he

theorem lowerBooleanEquality_correct (unequal : Bool) {left right : LeanExe.IR.Cond}
    {store : LeanExe.IR.ScalarStore} {a b : Bool}
    (first : left.ScalarEval store a store) (second : right.ScalarEval store b store) :
    (lowerBooleanEquality unequal left right).ScalarEval store (if unequal then a != b else a == b) store := by
  have result := lowerComparison_correct (if unequal then .bne else .beq)
    (guardWord_correct first) (guardWord_correct second)
  cases unequal <;> cases a <;> cases b <;> exact result

theorem lowerBooleanEquality_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (unequal : Bool) (left right : LeanExe.IR.Cond)
    (first : ∀ t e, P t → P e → P (.ite left t e))
    (second : ∀ t e, P t → P e → P (.ite right t e)) :
    ∀ t e, P t → P e → P (.ite (lowerBooleanEquality unequal left right) t e) := by
  intro t e ht he
  exact choice (if unequal then .bne else .beq) _ _ _ _
    (first _ _ (literal 1) (literal 0)) (second _ _ (literal 1) (literal 0)) ht he

theorem junctionPrimitive_denote (op : Junction) (left right : Bool) :
    (junctionPrimitive op).denote (Bool.toUInt64 left) (Bool.toUInt64 right) =
      Bool.toUInt64 (op.denote left right) := by
  cases op <;> cases left <;> cases right <;> rfl

theorem lowerJunction_correct (op : Junction) {left right : LeanExe.IR.Cond}
    {store : LeanExe.IR.ScalarStore} {a b : Bool}
    (first : left.ScalarEval store a store) (second : right.ScalarEval store b store) :
    (lowerJunction op left right).ScalarEval store (op.denote a b) store := by
  have result := (junctionPrimitive op).lower_correct (guardWord_correct first) (guardWord_correct second)
  rw [junctionPrimitive_denote] at result
  exact wordGuard_correct result

/-- Closure under existing scalar operators suffices for compound guards. -/
theorem lowerJunction_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (op : Junction) (left right : LeanExe.IR.Cond)
    (first : ∀ t e, P t → P e → P (.ite left t e))
    (second : ∀ t e, P t → P e → P (.ite right t e))
    (t e : LeanExe.IR.Expr) (ht : P t) (he : P e) :
    P (.ite (lowerJunction op left right) t e) := by
  exact choice .eq _ _ _ _
    (binary _ _ _ (first _ _ (literal 1) (literal 0)) (second _ _ (literal 1) (literal 0)))
    (literal 1) ht he

/-- A literal guard is known at compilation and uses existing word equality. -/
def lowerGuardLiteral (value : Bool) : LeanExe.IR.Cond :=
  .eqU64 (.u64 (if value then 1 else 0)) (.u64 1)

theorem lowerGuardLiteral_correct (value : Bool) (store : LeanExe.IR.ScalarStore) :
    (lowerGuardLiteral value).ScalarEval store value store := by
  cases value <;> exact .eq .const .const

theorem lowerGuardLiteral_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (value : Bool) : ∀ t e, P t → P e → P (.ite (lowerGuardLiteral value) t e) := by
  intro t e ht he
  exact choice .eq _ _ _ _ (literal _) (literal 1) ht he

/-- Each source Not wrapper tests the previous Boolean word against zero. -/
def lowerGuardNegations : Nat → LeanExe.IR.Cond → LeanExe.IR.Cond
  | 0, condition => condition
  | n + 1, condition => .eqU64 (guardWord (lowerGuardNegations n condition)) (.u64 0)

theorem lowerGuardNegations_correct (n : Nat) {condition : LeanExe.IR.Cond}
    {store : LeanExe.IR.ScalarStore} {value : Bool}
    (evaluated : condition.ScalarEval store value store) :
    (lowerGuardNegations n condition).ScalarEval store
      (LeanExe.Source.Scalar.GuardNegation.denote n value) store := by
  induction n with
  | zero => exact evaluated
  | succ n ih =>
    have result := LeanExe.IR.Cond.ScalarEval.eq (guardWord_correct ih) (LeanExe.IR.Expr.ScalarEval.const (n := 0))
    have negates (b : Bool) : (Bool.toUInt64 b == UInt64.ofNat 0) = !b := by cases b <;> rfl
    rw [negates] at result
    exact result

theorem lowerGuardNegations_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (n : Nat) (condition : LeanExe.IR.Cond)
    (preserve : ∀ t e, P t → P e → P (.ite condition t e)) :
    ∀ t e, P t → P e → P (.ite (lowerGuardNegations n condition) t e) := by
  induction n with
  | zero => exact preserve
  | succ n ih =>
    intro t e ht he
    exact choice .eq _ _ _ _ (ih _ _ (literal 1) (literal 0)) (literal 0) ht he

end LeanExe.Extract.Core
