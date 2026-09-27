import LeanExe.Source.ScalarGuardLiteral
import LeanExe.Source.ScalarBooleanPropositionLeaf
import LeanExe.Source.ScalarGuardLet

namespace LeanExe.Source.Scalar

/-- A guard tree retains each original scalar operand and its comparison syntax. -/
inductive Guard where
  | literal (value : GuardLiteral)
  | compare (op : Comparison) (left right : Lean.Expr)
  | junction (negations : Nat) (op : Junction) (left right : Guard)
  | boolean (propNegations boolNegations : Nat) (op : Junction) (left right : BooleanGuard)
  | savedLeft (negations : Nat) (op : Junction) (left : BooleanPropositionLeaf) (right : Guard)
  | savedRight (negations : Nat) (op : Junction) (left : Guard) (right : BooleanPropositionLeaf)
  | savedBoth (negations : Nat) (op : Junction) (left right : BooleanPropositionLeaf)
  | letGuard (negations : Nat) (binding : GuardLet) (body : Guard)
  | letSaved (negations : Nat) (binding : GuardLet) (body : SavedBooleanGuard)
  | localNegation (negations : Nat) (value : BooleanPropositionLeaf)
  deriving Repr

namespace Guard

def operands : Guard → List Lean.Expr
  | .literal _ => []
  | .compare _ a b => [a, b]
  | .junction _ _ a b => a.operands ++ b.operands
  | .boolean _ n op a b => (BooleanGuard.junction n op a b).operands
  | .savedLeft _ _ a b => a.operands ++ b.operands
  | .savedRight _ _ a b => a.operands ++ b.operands
  | .savedBoth _ _ a b => a.operands ++ b.operands
  | .letGuard _ binding body => binding.operand :: body.operands.map binding.wrap
  | .letSaved _ binding body => binding.operand :: [binding.wrap body.operand]
  | .localNegation _ value => value.operands

def condition : Guard → Lean.Expr
  | .literal value => value.condition
  | .compare op a b => op.condition a b
  | .junction n op a b => GuardNegation.condition n (op.condition a.condition b.condition)
  | .boolean m n op a b => GuardNegation.condition m (BooleanGuard.junction n op a b).condition
  | .savedLeft n op a b => GuardNegation.condition n (op.condition a.condition b.condition)
  | .savedRight n op a b => GuardNegation.condition n (op.condition a.condition b.condition)
  | .savedBoth n op a b => GuardNegation.condition n (op.condition a.condition b.condition)
  | .letGuard n binding body => GuardNegation.condition n (binding.wrap body.condition)
  | .letSaved n binding body => GuardNegation.condition n (binding.wrap body.condition)
  | .localNegation n value => GuardNegation.condition (n + 1) value.condition

def evidence : Guard → Lean.Expr
  | .literal value => value.evidence
  | .compare op a b => op.evidence a b
  | .junction n op a b => GuardNegation.evidence n (op.condition a.condition b.condition)
      (op.evidence a.condition b.condition a.evidence b.evidence)
  | .boolean m n op a b => GuardNegation.evidence m (BooleanGuard.junction n op a b).condition
      (BooleanGuard.junction n op a b).evidence
  | .savedLeft n op a b => GuardNegation.evidence n (op.condition a.condition b.condition)
      (op.evidence a.condition b.condition a.evidence b.evidence)
  | .savedRight n op a b => GuardNegation.evidence n (op.condition a.condition b.condition)
      (op.evidence a.condition b.condition a.evidence b.evidence)
  | .savedBoth n op a b => GuardNegation.evidence n (op.condition a.condition b.condition)
      (op.evidence a.condition b.condition a.evidence b.evidence)
  | .letGuard n binding body => GuardNegation.evidence n (binding.wrap body.condition) (binding.evidence body.evidence)
  | .letSaved n binding body => GuardNegation.evidence n (binding.wrap body.condition) (binding.evidence body.evidence)
  | .localNegation n value => GuardNegation.evidence (n + 1) value.condition value.evidence

def denote (native : Lean.Expr → UInt64) : Guard → Bool
  | .literal value => value.denote
  | .compare op a b => op.denote (native a) (native b)
  | .junction n op a b => GuardNegation.denote n (op.denote (a.denote native) (b.denote native))
  | .boolean m n op a b => GuardNegation.denote m ((BooleanGuard.junction n op a b).denote native)
  | .savedLeft n op a b => GuardNegation.denote n (op.denote (a.denote native) (b.denote native))
  | .savedRight n op a b => GuardNegation.denote n (op.denote (a.denote native) (b.denote native))
  | .savedBoth n op a b => GuardNegation.denote n (op.denote (a.denote native) (b.denote native))
  | .letGuard n binding body => GuardNegation.denote n (body.denote (fun operand => native (binding.wrap operand)))
  | .letSaved n binding body => GuardNegation.denote n (body.denote (fun operand => native (binding.wrap operand)))
  | .localNegation n value => GuardNegation.denote (n + 1) (value.denote native)

def negate : Guard → Guard
  | .literal value => .literal value.negate
  | .compare op a b => .compare (.negate op) a b
  | .junction n op a b => .junction (n + 1) op a b
  | .boolean m n op a b => .boolean (m + 1) n op a b
  | .savedLeft n op a b => .savedLeft (n + 1) op a b
  | .savedRight n op a b => .savedRight (n + 1) op a b
  | .savedBoth n op a b => .savedBoth (n + 1) op a b
  | .letGuard n binding body => .letGuard (n + 1) binding body
  | .letSaved n binding body => .letSaved (n + 1) binding body
  | .localNegation n value => .localNegation (n + 1) value

theorem negate_condition (guard : Guard) :
    guard.negate.condition = .app (.const ``Not []) guard.condition := by
  cases guard with
  | literal value => exact value.negate_condition
  | _ => rfl

theorem condition_min_size (guard : Guard) :
    sizeOf (.const ``True [] : Lean.Expr) ≤ sizeOf guard.condition := by
  induction guard with
  | literal value => exact value.condition_min_size
  | compare op a b => exact op.condition_min_size a b
  | boolean m n op a b =>
    exact Nat.le_trans (BooleanGuard.junction n op a b).condition_min_size (GuardNegation.condition_size m _)
  | junction n op a b iha ihb =>
    apply Nat.le_trans _ (GuardNegation.condition_size n _)
    have bound := iha
    cases op <;> simp [Junction.condition] at bound ⊢ <;> omega
  | savedLeft n op a b ihb =>
    apply Nat.le_trans _ (GuardNegation.condition_size n _)
    have bound := a.condition_min_size
    cases op <;> simp [Junction.condition] at bound ⊢ <;> omega
  | savedRight n op a b iha =>
    apply Nat.le_trans _ (GuardNegation.condition_size n _)
    have bound := iha
    cases op <;> simp [Junction.condition] at bound ⊢ <;> omega
  | savedBoth n op a b =>
    apply Nat.le_trans _ (GuardNegation.condition_size n _)
    have bound := a.condition_min_size
    cases op <;> simp [Junction.condition] at bound ⊢ <;> omega
  | letGuard n binding body ih =>
    apply Nat.le_trans _ (GuardNegation.condition_size n _)
    have bound := ih
    simp [GuardLet.wrap] at bound ⊢; omega
  | letSaved n binding body =>
    apply Nat.le_trans _ (GuardNegation.condition_size n _)
    have bound := body.condition_min_size
    simp [GuardLet.wrap] at bound ⊢; omega
  | localNegation n value =>
    exact Nat.le_trans value.condition_min_size (GuardNegation.condition_size (n + 1) _)

theorem operands_size (guard : Guard) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf guard.condition + guardOperandOverhead := by
  induction guard generalizing operand with
  | literal => simp [operands] at member
  | compare op a b =>
    simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
    have bounds := op.operands_size a b
    simp only [condition]
    rcases member with rfl | rfl
    · exact Nat.lt_of_lt_of_le bounds.1 (by omega)
    · exact Nat.lt_of_lt_of_le bounds.2 (by omega)
  | junction n op a b iha ihb =>
    apply Nat.lt_of_lt_of_le _ (Nat.add_le_add_right (GuardNegation.condition_size n _) guardOperandOverhead)
    simp only [operands, List.mem_append] at member
    cases op <;> simp only [Junction.condition]
    all_goals rcases member with member | member
    all_goals first
      | (have h := iha member; clear iha; simp_all; omega)
      | (have h := ihb member; clear ihb; simp_all; omega)
  | boolean m n op a b =>
    apply Nat.lt_of_lt_of_le _ (Nat.add_le_add_right (GuardNegation.condition_size m _) guardOperandOverhead)
    have bound := (BooleanGuard.junction n op a b).operands_size (operand := operand) member
    simp only [BooleanGuard.condition]
    simp_all; omega
  | savedLeft n op a b ihb =>
    apply Nat.lt_of_lt_of_le _ (Nat.add_le_add_right (GuardNegation.condition_size n _) guardOperandOverhead)
    rcases List.mem_append.mp member with member | member
    · exact a.operands_junction_left op b.condition b.condition_min_size member
    · have bound := ihb member
      cases op <;> simp [Junction.condition] at * <;> omega
  | savedRight n op a b iha =>
    apply Nat.lt_of_lt_of_le _ (Nat.add_le_add_right (GuardNegation.condition_size n _) guardOperandOverhead)
    rcases List.mem_append.mp member with member | member
    · have bound := iha member
      cases op <;> simp [Junction.condition] at * <;> omega
    · exact b.operands_junction_right op a.condition a.condition_min_size member
  | savedBoth n op a b =>
    apply Nat.lt_of_lt_of_le _ (Nat.add_le_add_right (GuardNegation.condition_size n _) guardOperandOverhead)
    rcases List.mem_append.mp member with member | member
    · exact a.operands_junction_left op b.condition b.condition_min_size member
    · exact b.operands_junction_right op a.condition a.condition_min_size member
  | letGuard n binding body ih =>
    apply Nat.lt_of_lt_of_le _ (Nat.add_le_add_right (GuardNegation.condition_size n _) guardOperandOverhead)
    simp only [operands, List.mem_cons, List.mem_map] at member
    rcases member with rfl | ⟨inner, member, rfl⟩
    · exact binding.operand_size body.condition body.condition_min_size
    · have bound := ih member
      simp [GuardLet.wrap] at *; omega
  | letSaved n binding body =>
    apply Nat.lt_of_lt_of_le _ (Nat.add_le_add_right (GuardNegation.condition_size n _) guardOperandOverhead)
    simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact binding.operand_size body.condition body.condition_min_size
    · exact Nat.lt_of_lt_of_le (binding.wrap_size body.operand_size) (by omega)
  | localNegation n value => exact value.operands_negation n member

end Guard

namespace BooleanGuard

/-- Preserve scalar operands and Boolean meaning while sharing guard lowering. -/
def asGuard : BooleanGuard → Guard
  | .literal n value => .literal (.boolean 0 n value)
  | .compare op a b => .compare (comparison op) a b
  | .junction n op a b => .junction n op a.asGuard b.asGuard

@[simp] theorem asGuard_operands (guard : BooleanGuard) :
    guard.asGuard.operands = guard.operands := by
  induction guard <;> simp_all [asGuard, operands, Guard.operands]

theorem asGuard_denote (guard : BooleanGuard) (native : Lean.Expr → UInt64) :
    guard.asGuard.denote native = guard.denote native := by
  induction guard <;> simp_all [asGuard, denote, Guard.denote, GuardLiteral.denote, GuardNegation.denote, comparison_denote]

end BooleanGuard
end LeanExe.Source.Scalar
