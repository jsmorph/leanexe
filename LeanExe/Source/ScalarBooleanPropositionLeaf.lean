import LeanExe.Source.ScalarGuardLet

namespace LeanExe.Source.Scalar

/-- Boolean truth and relations used inside compound propositions. -/
inductive BooleanPropositionLeaf where
  | truth (value : SavedBooleanGuard)
  | relation (unequal : Bool) (left right : Lean.Expr)
      (nontruth : unequal = false → right ≠ .const ``Bool.true [])
  deriving Repr

instance : Coe SavedBooleanGuard BooleanPropositionLeaf := ⟨.truth⟩

namespace BooleanPropositionLeaf

def condition : BooleanPropositionLeaf → Lean.Expr
  | .truth value => value.condition
  | .relation unequal left right _ =>
      .app (.app (.app (.const (if unequal then ``Ne else ``Eq) [.succ .zero])
        (.const ``Bool [])) left) right

def evidence : BooleanPropositionLeaf → Lean.Expr
  | .truth value => value.evidence
  | .relation unequal left right _ =>
      let equality := Lean.Expr.app (.app (.const ``instDecidableEqBool []) left) right
      if unequal then
        .app (.app (.const ``instDecidableNot [])
          (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) left) right)) equality
      else equality

def operands : BooleanPropositionLeaf → List Lean.Expr
  | .truth value => [value.operand]
  | .relation _ left right _ =>
      [.app (.const ``Bool.toUInt64 []) left, .app (.const ``Bool.toUInt64 []) right]

def denote (value : BooleanPropositionLeaf) (native : Lean.Expr → UInt64) : Bool :=
  match value with
  | .truth value => value.denote native
  | .relation unequal left right _ =>
      if unequal then native (.app (.const ``Bool.toUInt64 []) left) !=
        native (.app (.const ``Bool.toUInt64 []) right)
      else native (.app (.const ``Bool.toUInt64 []) left) ==
        native (.app (.const ``Bool.toUInt64 []) right)

/-- Comparing encoded Booleans gives the original Eq/Ne proposition's decision. -/
theorem relation_denote (unequal : Bool) (left right : Lean.Expr)
    (nontruth : unequal = false → right ≠ .const ``Bool.true [])
    (native : Lean.Expr → UInt64) (a b : Bool)
    (first : native (.app (.const ``Bool.toUInt64 []) left) = a.toUInt64)
    (second : native (.app (.const ``Bool.toUInt64 []) right) = b.toUInt64) :
    (relation unequal left right nontruth).denote native =
      decide (if unequal then a ≠ b else a = b) := by
  cases unequal <;> cases a <;> cases b <;> simp [denote, first, second]
  all_goals decide

theorem condition_min_size (value : BooleanPropositionLeaf) :
    sizeOf (.const ``True [] : Lean.Expr) ≤ sizeOf value.condition := by
  cases value with
  | truth value => exact value.condition_min_size
  | relation unequal left right _ =>
    have eqSize : sizeOf (.const ``True [] : Lean.Expr) ≤
      sizeOf (.const ``Eq [.succ .zero] : Lean.Expr) + sizeOf (.const ``Bool [] : Lean.Expr) := by decide
    have neSize : sizeOf (.const ``True [] : Lean.Expr) ≤
      sizeOf (.const ``Ne [.succ .zero] : Lean.Expr) + sizeOf (.const ``Bool [] : Lean.Expr) := by decide
    cases unequal <;> simp [condition] at * <;> omega

/-- The conversion head is bounded against the original Boolean proposition. -/
theorem operands_size (value : BooleanPropositionLeaf) {operand : Lean.Expr}
    (member : operand ∈ value.operands) :
    sizeOf operand < sizeOf value.condition + guardOperandOverhead := by
  cases value with
  | truth value =>
    simp only [operands, List.mem_singleton] at member
    subst operand
    exact Nat.lt_of_lt_of_le value.operand_size (by simp [condition])
  | relation unequal left right _ =>
    simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
    have heads : sizeOf (.const ``Bool.toUInt64 [] : Lean.Expr) <
      sizeOf (.const ``Ne [.succ .zero] : Lean.Expr) + sizeOf (.const ``Bool [] : Lean.Expr) + guardOperandOverhead := by decide
    have eqLarger : sizeOf (.const ``Ne [.succ .zero] : Lean.Expr) ≤
      sizeOf (.const ``Eq [.succ .zero] : Lean.Expr) := by decide
    rcases member with rfl | rfl
    all_goals cases unequal <;> simp [condition] at * <;> omega

theorem operands_junction_left (value : BooleanPropositionLeaf) (op : Junction)
    (other : Lean.Expr) (_minimum : sizeOf (.const ``True [] : Lean.Expr) ≤ sizeOf other)
    {operand : Lean.Expr} (member : operand ∈ value.operands) :
    sizeOf operand < sizeOf (op.condition value.condition other) + guardOperandOverhead := by
  have bound := value.operands_size member
  have heads : sizeOf (.const ``Not [] : Lean.Expr) ≤ sizeOf (.const ``True [] : Lean.Expr) := by decide
  cases op <;> simp [Junction.condition] at * <;> omega

theorem operands_junction_right (value : BooleanPropositionLeaf) (op : Junction)
    (other : Lean.Expr) (_minimum : sizeOf (.const ``True [] : Lean.Expr) ≤ sizeOf other)
    {operand : Lean.Expr} (member : operand ∈ value.operands) :
    sizeOf operand < sizeOf (op.condition other value.condition) + guardOperandOverhead := by
  have bound := value.operands_size member
  have heads : sizeOf (.const ``Not [] : Lean.Expr) ≤ sizeOf (.const ``True [] : Lean.Expr) := by decide
  cases op <;> simp [Junction.condition] at * <;> omega

theorem operands_negation (value : BooleanPropositionLeaf) (negations : Nat)
    {operand : Lean.Expr} (member : operand ∈ value.operands) :
    sizeOf operand < sizeOf (GuardNegation.condition (negations + 1) value.condition) + guardOperandOverhead := by
  have bound := value.operands_size member
  have larger := GuardNegation.condition_size negations value.condition
  simp [GuardNegation.condition] at *
  omega

end BooleanPropositionLeaf
end LeanExe.Source.Scalar
