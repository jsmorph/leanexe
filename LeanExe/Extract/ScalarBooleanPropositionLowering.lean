import LeanExe.Source.ScalarBooleanPropositionLeaf
import LeanExe.Extract.ScalarBooleanGuard

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar (BooleanPropositionLeaf)

/-- Lower a Boolean proposition from recursively checked scalar operands. -/
def extractBooleanPropositionLeaf : (value : BooleanPropositionLeaf) →
    ((operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr) → Option LeanExe.IR.Cond
  | .truth value, compile => do
      let operand ← compile value.operand (by simp [BooleanPropositionLeaf.operands])
      pure (wordGuard operand)
  | .relation unequal left right _, compile => do
      let first ← compile (.app (.const ``Bool.toUInt64 []) left) (by simp [BooleanPropositionLeaf.operands])
      let second ← compile (.app (.const ``Bool.toUInt64 []) right) (by simp [BooleanPropositionLeaf.operands])
      pure (lowerComparison (if unequal then .bne else .beq) first second)

theorem extractBooleanPropositionLeaf_accepts (value : BooleanPropositionLeaf)
    (compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr)
    (total : ∀ operand member, ∃ target, compile operand member = some target) :
    ∃ target, extractBooleanPropositionLeaf value compile = some target := by
  cases value with
  | truth value =>
    obtain ⟨target, found⟩ := total value.operand (by simp [BooleanPropositionLeaf.operands])
    exact ⟨wordGuard target, by simp [extractBooleanPropositionLeaf, found]⟩
  | relation unequal left right nontruth =>
    obtain ⟨first, hf⟩ := total (.app (.const ``Bool.toUInt64 []) left) (by simp [BooleanPropositionLeaf.operands])
    obtain ⟨second, hs⟩ := total (.app (.const ``Bool.toUInt64 []) right) (by simp [BooleanPropositionLeaf.operands])
    exact ⟨lowerComparison (if unequal then .bne else .beq) first second, by simp [extractBooleanPropositionLeaf, hf, hs]⟩

theorem extractBooleanPropositionLeaf_operands (value : BooleanPropositionLeaf)
    (compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanPropositionLeaf value compile = some target) :
    ∀ operand member, ∃ expression, compile operand member = some expression := by
  cases value with
  | truth value =>
    simp only [extractBooleanPropositionLeaf, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨expression, found, _⟩ := compiled
    intro operand member
    simp only [BooleanPropositionLeaf.operands, List.mem_singleton] at member
    subst operand
    exact ⟨expression, found⟩
  | relation unequal left right nontruth =>
    simp only [extractBooleanPropositionLeaf, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hf, second, hs, _⟩ := compiled
    intro operand member
    simp only [BooleanPropositionLeaf.operands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨first, hf⟩
    · exact ⟨second, hs⟩

theorem extractBooleanPropositionLeaf_correct (value : BooleanPropositionLeaf)
    (compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr)
    (native : Lean.Expr → UInt64) {target : LeanExe.IR.Cond} {store : LeanExe.IR.ScalarStore}
    (compiled : extractBooleanPropositionLeaf value compile = some target)
    (meanings : ∀ operand member expression, compile operand member = some expression →
      expression.ScalarEval store (native operand) store) :
    target.ScalarEval store (value.denote native) store := by
  cases value with
  | truth value =>
    simp only [extractBooleanPropositionLeaf, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨expression, found, rfl⟩ := compiled
    exact .eq (meanings _ _ _ found) .const
  | relation unequal left right nontruth =>
    simp only [extractBooleanPropositionLeaf, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hf, second, hs, rfl⟩ := compiled
    cases unequal with
    | false => exact lowerComparison_correct .beq (meanings _ _ _ hf) (meanings _ _ _ hs)
    | true => exact lowerComparison_correct .bne (meanings _ _ _ hf) (meanings _ _ _ hs)

theorem extractBooleanPropositionLeaf_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (value : BooleanPropositionLeaf)
    (compile : (operand : Lean.Expr) → operand ∈ value.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanPropositionLeaf value compile = some target)
    (operands : ∀ operand member expression, compile operand member = some expression → P expression) :
    ∀ t e, P t → P e → P (.ite target t e) := by
  cases value with
  | truth value =>
    simp only [extractBooleanPropositionLeaf, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨expression, found, rfl⟩ := compiled
    exact fun t e ht he => choice .eq _ _ t e (operands _ _ _ found) (literal 1) ht he
  | relation unequal left right nontruth =>
    simp only [extractBooleanPropositionLeaf, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hf, second, hs, rfl⟩ := compiled
    exact fun t e ht he => choice _ _ _ t e (operands _ _ _ hf) (operands _ _ _ hs) ht he

end LeanExe.Extract.Core
