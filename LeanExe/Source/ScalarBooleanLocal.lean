import LeanExe.Source.ScalarBooleanGuard

namespace LeanExe.Source.Scalar

/-- Boolean expressions with explicit lexical references, distinct from scalar operands. -/
inductive BooleanLocal where
  | var (negations index : Nat)
  | literal (negations : Nat) (value : Bool)
  | compare (op : BooleanComparison) (left right : Lean.Expr)
  | junction (negations : Nat) (op : Junction) (left right : BooleanLocal)
  deriving Repr

namespace BooleanLocal

def operands : BooleanLocal → List Lean.Expr
  | .var _ _ => []
  | .literal _ _ => []
  | .compare _ a b => [a, b]
  | .junction _ _ a b => a.operands ++ b.operands

def expr : BooleanLocal → Lean.Expr
  | .var n index => BooleanGuardNegation.expr n (.bvar index)
  | .literal n value => BooleanGuardNegation.expr n (booleanLiteralExpr value)
  | .compare op a b => op.expr a b
  | .junction n op a b => BooleanGuardNegation.expr n (op.booleanExpr a.expr b.expr)

def denote (native : Lean.Expr → UInt64) (booleans : Nat → Bool) : BooleanLocal → Bool
  | .var n index => GuardNegation.denote n (booleans index)
  | .literal n value => GuardNegation.denote n value
  | .compare op a b => op.denote (native a) (native b)
  | .junction n op a b => GuardNegation.denote n (op.denote (a.denote native booleans) (b.denote native booleans))

def negate : BooleanLocal → BooleanLocal
  | .var n index => .var (n + 1) index
  | .literal n value => .literal (n + 1) value
  | .compare op a b => .compare (.negate op) a b
  | .junction n op a b => .junction (n + 1) op a b

theorem negate_expr (guard : BooleanLocal) :
    guard.negate.expr = .app (.const ``Bool.not []) guard.expr := by
  cases guard <;> rfl

theorem operands_size (guard : BooleanLocal) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf guard.expr := by
  induction guard with
  | literal | var => simp [operands] at member
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

def variables : BooleanLocal → List Nat
  | .var _ index => [index]
  | .literal .. | .compare .. => []
  | .junction _ _ a b => a.variables ++ b.variables

def condition (value : BooleanLocal) : Lean.Expr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) value.expr) (.const ``Bool.true [])

def evidence (value : BooleanLocal) : Lean.Expr :=
  .app (.app (.const ``instDecidableEqBool []) value.expr) (.const ``Bool.true [])

end BooleanLocal
/-- A condition using at least one Boolean binding. Closed guards retain their
existing source and compiler paths. -/
structure BooleanLocalGuard where
  value : BooleanLocal
  nonempty : value.variables ≠ []

namespace BooleanLocalGuard
abbrev condition (guard : BooleanLocalGuard) := guard.value.condition
abbrev evidence (guard : BooleanLocalGuard) := guard.value.evidence

def branch (guard : BooleanLocalGuard) (type t e : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type)
    guard.condition) guard.evidence) t) e
def dependentBranch (guard : BooleanLocalGuard) (type : Lean.Expr)
    (tn fn : Lean.Name) (tb fb : Lean.BinderInfo) (t e : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) type)
    guard.condition) guard.evidence)
      (.lam tn guard.condition t tb))
      (.lam fn (.app (.const ``Not []) guard.condition) e fb)

end BooleanLocalGuard

end LeanExe.Source.Scalar
