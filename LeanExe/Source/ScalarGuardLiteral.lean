import LeanExe.Source.ScalarBooleanGuard

namespace LeanExe.Source.Scalar

/-- Preserve propositional and Boolean literal syntax and all negation wrappers. -/
inductive GuardLiteral where
  | proposition (negations : Nat) (value : Bool)
  | boolean (propNegations boolNegations : Nat) (value : Bool)
  deriving Repr

namespace GuardLiteral

def propositionExpr (value : Bool) : Lean.Expr :=
  .const (if value then ``True else ``False) []

def propositionEvidence (value : Bool) : Lean.Expr :=
  .const (if value then ``instDecidableTrue else ``instDecidableFalse) []

def condition : GuardLiteral → Lean.Expr
  | .proposition n value => GuardNegation.condition n (propositionExpr value)
  | .boolean m n value => GuardNegation.condition m (BooleanGuard.literal n value).condition

def evidence : GuardLiteral → Lean.Expr
  | .proposition n value => GuardNegation.evidence n (propositionExpr value) (propositionEvidence value)
  | .boolean m n value => GuardNegation.evidence m (BooleanGuard.literal n value).condition
      (BooleanGuard.literal n value).evidence

def denote : GuardLiteral → Bool
  | .proposition n value => GuardNegation.denote n value
  | .boolean m n value => GuardNegation.denote m (GuardNegation.denote n value)

def negate : GuardLiteral → GuardLiteral
  | .proposition n value => .proposition (n + 1) value
  | .boolean m n value => .boolean (m + 1) n value

theorem negate_condition (literal : GuardLiteral) :
    literal.negate.condition = .app (.const ``Not []) literal.condition := by
  cases literal <;> rfl

end GuardLiteral
end LeanExe.Source.Scalar
