import LeanExe.Source.ScalarGuardLiteral

namespace LeanExe.Source.Scalar

/-- A guard tree retains each original scalar operand and its comparison syntax. -/
inductive Guard where
  | literal (value : GuardLiteral)
  | compare (op : Comparison) (left right : Lean.Expr)
  | junction (negations : Nat) (op : Junction) (left right : Guard)
  | boolean (propNegations boolNegations : Nat) (op : Junction) (left right : BooleanGuard)
  deriving Repr

namespace Guard

def operands : Guard → List Lean.Expr
  | .literal _ => []
  | .compare _ a b => [a, b]
  | .junction _ _ a b => a.operands ++ b.operands
  | .boolean _ n op a b => (BooleanGuard.junction n op a b).operands

def condition : Guard → Lean.Expr
  | .literal value => value.condition
  | .compare op a b => op.condition a b
  | .junction n op a b => GuardNegation.condition n (op.condition a.condition b.condition)
  | .boolean m n op a b => GuardNegation.condition m (BooleanGuard.junction n op a b).condition

def evidence : Guard → Lean.Expr
  | .literal value => value.evidence
  | .compare op a b => op.evidence a b
  | .junction n op a b => GuardNegation.evidence n (op.condition a.condition b.condition)
      (op.evidence a.condition b.condition a.evidence b.evidence)
  | .boolean m n op a b => GuardNegation.evidence m (BooleanGuard.junction n op a b).condition
      (BooleanGuard.junction n op a b).evidence

def denote (native : Lean.Expr → UInt64) : Guard → Bool
  | .literal value => value.denote
  | .compare op a b => op.denote (native a) (native b)
  | .junction n op a b => GuardNegation.denote n (op.denote (a.denote native) (b.denote native))
  | .boolean m n op a b => GuardNegation.denote m ((BooleanGuard.junction n op a b).denote native)

def negate : Guard → Guard
  | .literal value => .literal value.negate
  | .compare op a b => .compare (.negate op) a b
  | .junction n op a b => .junction (n + 1) op a b
  | .boolean m n op a b => .boolean (m + 1) n op a b

theorem negate_condition (guard : Guard) :
    guard.negate.condition = .app (.const ``Not []) guard.condition := by
  cases guard with
  | literal value => exact value.negate_condition
  | _ => rfl

theorem operands_size (guard : Guard) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf guard.condition := by
  induction guard with
  | literal => simp [operands] at member
  | compare op a b =>
    simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
    have bounds := op.operands_size a b
    rcases member with rfl | rfl
    · exact bounds.1
    · exact bounds.2
  | junction n op a b iha ihb =>
    apply Nat.lt_of_lt_of_le _ (GuardNegation.condition_size n _)
    simp only [operands, List.mem_append] at member
    cases op <;> simp only [Junction.condition]
    all_goals rcases member with member | member
    all_goals first
      | (have h := iha member; simp_all; omega)
      | (have h := ihb member; simp_all; omega)
  | boolean m n op a b =>
    apply Nat.lt_of_lt_of_le _ (GuardNegation.condition_size m _)
    have bound := (BooleanGuard.junction n op a b).operands_size (operand := operand) member
    simp only [BooleanGuard.condition]
    simp_all; omega

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
