import LeanExe.Source.ScalarGuardCommon

namespace LeanExe.Source.Scalar

namespace BooleanGuardNegation

def expr : Nat → Lean.Expr → Lean.Expr
  | 0, expression => expression
  | n + 1, expression => .app (.const ``Bool.not []) (expr n expression)

theorem expr_size (n : Nat) (expression : Lean.Expr) :
    sizeOf expression ≤ sizeOf (expr n expression) := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => simp only [expr]; simp_all; omega

end BooleanGuardNegation

def Junction.booleanExpr (op : Junction) (a b : Lean.Expr) : Lean.Expr :=
  .app (.app (.const (match op with | .conjunction => ``Bool.and | .disjunction => ``Bool.or) []) a) b

def booleanLiteralExpr (value : Bool) : Lean.Expr :=
  .const (if value then ``Bool.true else ``Bool.false) []

/-- Concrete Bool expressions over literals and standard UInt64 comparisons. -/
inductive BooleanGuard where
  | literal (negations : Nat) (value : Bool)
  | compare (op : BooleanComparison) (left right : Lean.Expr)
  | junction (negations : Nat) (op : Junction) (left right : BooleanGuard)
  deriving Repr

namespace BooleanGuard

def operands : BooleanGuard → List Lean.Expr
  | .literal _ _ => []
  | .compare _ a b => [a, b]
  | .junction _ _ a b => a.operands ++ b.operands

def expr : BooleanGuard → Lean.Expr
  | .literal n value => BooleanGuardNegation.expr n (booleanLiteralExpr value)
  | .compare op a b => op.expr a b
  | .junction n op a b => BooleanGuardNegation.expr n (op.booleanExpr a.expr b.expr)

def denote (native : Lean.Expr → UInt64) : BooleanGuard → Bool
  | .literal n value => GuardNegation.denote n value
  | .compare op a b => op.denote (native a) (native b)
  | .junction n op a b => GuardNegation.denote n (op.denote (a.denote native) (b.denote native))

def negate : BooleanGuard → BooleanGuard
  | .literal n value => .literal (n + 1) value
  | .compare op a b => .compare (.negate op) a b
  | .junction n op a b => .junction (n + 1) op a b

theorem negate_expr (guard : BooleanGuard) :
    guard.negate.expr = .app (.const ``Bool.not []) guard.expr := by
  cases guard <;> rfl

theorem operands_size (guard : BooleanGuard) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf guard.expr := by
  induction guard with
  | literal => simp [operands] at member
  | compare op a b =>
    simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
    have bounds := op.operands_size a b
    rcases member with rfl | rfl
    · exact bounds.1
    · exact bounds.2
  | junction n op a b iha ihb =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    simp only [operands, List.mem_append] at member
    cases op <;> simp only [Junction.booleanExpr]
    all_goals rcases member with member | member
    all_goals first
      | (have h := iha member; simp_all; omega)
      | (have h := ihb member; simp_all; omega)

/-- Both guard syntaxes use the same native comparison operations. -/
def comparison : BooleanComparison → Comparison
  | .eq => .beq
  | .ne => .bne
  | .negate op => .boolNot op

theorem comparison_denote (op : BooleanComparison) (x y : UInt64) :
    (comparison op).denote x y = op.denote x y := by
  cases op <;> rfl

def condition (guard : BooleanGuard) : Lean.Expr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) guard.expr) (.const ``Bool.true [])

def evidence (guard : BooleanGuard) : Lean.Expr :=
  .app (.app (.const ``instDecidableEqBool []) guard.expr) (.const ``Bool.true [])

end BooleanGuard
end LeanExe.Source.Scalar
