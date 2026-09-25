import LeanExe.Source.ScalarPropositionGuard

namespace LeanExe.Source.Scalar

/-- Standard Boolean-valued choice over a Boolean condition. -/
def booleanChoiceExpr (condition yes no : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) (.const ``Bool []))
    (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) condition) (.const ``Bool.true [])))
    (.app (.app (.const ``instDecidableEqBool []) condition) (.const ``Bool.true []))) yes) no

/-- Bool-valued decision with exact standard proposition and decision evidence. -/
def Guard.decisionExpr (guard : Guard) : Lean.Expr :=
  .app (.app (.const ``Decidable.decide []) guard.condition) guard.evidence

/-- Boolean expressions with explicit lexical references, distinct from scalar operands. -/
inductive BooleanLocal where
  | var (negations index : Nat)
  | literal (negations : Nat) (value : Bool)
  | compare (op : BooleanComparison) (left right : Lean.Expr)
  | junction (negations : Nat) (op : Junction) (left right : BooleanLocal)
  | choice (negations : Nat) (condition yes no : BooleanLocal)
  | proposition (negations : Nat) (guard : PropositionGuard) (yes no : BooleanLocal)
  | decision (negations : Nat) (guard : Guard)
  deriving Repr

namespace BooleanLocal

def operands : BooleanLocal → List Lean.Expr
  | .var _ _ => []
  | .literal _ _ => []
  | .compare _ a b => [a, b]
  | .junction _ _ a b => a.operands ++ b.operands
  | .choice _ c t e => c.operands ++ (t.operands ++ e.operands)
  | .proposition _ g t e => g.operands ++ (t.operands ++ e.operands)
  | .decision _ g => g.operands

def expr : BooleanLocal → Lean.Expr
  | .var n index => BooleanGuardNegation.expr n (.bvar index)
  | .literal n value => BooleanGuardNegation.expr n (booleanLiteralExpr value)
  | .compare op a b => op.expr a b
  | .junction n op a b => BooleanGuardNegation.expr n (op.booleanExpr a.expr b.expr)
  | .choice n c t e => BooleanGuardNegation.expr n (booleanChoiceExpr c.expr t.expr e.expr)
  | .proposition n g t e => BooleanGuardNegation.expr n (g.branch t.expr e.expr)
  | .decision n g => BooleanGuardNegation.expr n g.decisionExpr

def denote (native : Lean.Expr → UInt64) (booleans : Nat → Bool) : BooleanLocal → Bool
  | .var n index => GuardNegation.denote n (booleans index)
  | .literal n value => GuardNegation.denote n value
  | .compare op a b => op.denote (native a) (native b)
  | .junction n op a b => GuardNegation.denote n (op.denote (a.denote native booleans) (b.denote native booleans))
  | .choice n c t e => GuardNegation.denote n
      (if c.denote native booleans then t.denote native booleans else e.denote native booleans)
  | .proposition n g t e => GuardNegation.denote n
      (if g.denote native then t.denote native booleans else e.denote native booleans)
  | .decision n g => GuardNegation.denote n (g.denote native)

def negate : BooleanLocal → BooleanLocal
  | .var n index => .var (n + 1) index
  | .literal n value => .literal (n + 1) value
  | .compare op a b => .compare (.negate op) a b
  | .junction n op a b => .junction (n + 1) op a b
  | .choice n c t e => .choice (n + 1) c t e
  | .proposition n g t e => .proposition (n + 1) g t e
  | .decision n g => .decision (n + 1) g

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
  | choice n c t e ihc iht ihe =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    simp only [operands, List.mem_append] at member
    simp only [booleanChoiceExpr]
    rcases member with member | member | member
    · have h := ihc member; simp_all; omega
    · have h := iht member; simp_all; omega
    · have h := ihe member; simp_all; omega
  | proposition n g t e iht ihe =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    simp only [operands, List.mem_append] at member
    simp only [PropositionGuard.branch, PropositionGuard.condition]
    rcases member with member | member | member
    · have h := g.value.operands_size member; simp_all; omega
    · have h := iht member; simp_all; omega
    · have h := ihe member; simp_all; omega

  | decision n g =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    have bound := g.operands_size member
    simp only [Guard.decisionExpr]
    simp_all
    omega

def variables : BooleanLocal → List Nat
  | .var _ index => [index]
  | .literal .. | .compare .. | .decision .. => []
  | .junction _ _ a b => a.variables ++ b.variables
  | .choice _ c t e => c.variables ++ (t.variables ++ e.variables)
  | .proposition _ _ t e => t.variables ++ e.variables

/-- Whether this value needs the Boolean-local path beyond the closed guard grammar. -/
def extended : BooleanLocal → Bool
  | .var .. | .choice .. | .proposition .. | .decision .. => true
  | .literal .. | .compare .. => false
  | .junction _ _ a b => a.extended || b.extended

def condition (value : BooleanLocal) : Lean.Expr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) value.expr) (.const ``Bool.true [])

def evidence (value : BooleanLocal) : Lean.Expr :=
  .app (.app (.const ``instDecidableEqBool []) value.expr) (.const ``Bool.true [])

end BooleanLocal
/-- A condition using Boolean bindings or Boolean-valued choices. The preceding
closed guard forms retain their existing source and compiler paths. -/
structure BooleanLocalGuard where
  value : BooleanLocal
  expanded : value.extended = true

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
