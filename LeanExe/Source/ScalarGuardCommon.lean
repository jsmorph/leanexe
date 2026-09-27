import LeanExe.Source.ScalarComparison

namespace LeanExe.Source.Scalar

/-- The standard propositional connectives admitted by compound guards. -/
inductive Junction where
  | conjunction | disjunction
  deriving DecidableEq, Repr

namespace Junction

def denote : Junction → Bool → Bool → Bool
  | .conjunction => fun a b => a && b
  | .disjunction => fun a b => a || b

def condition (op : Junction) (a b : Lean.Expr) : Lean.Expr :=
  .app (.app (.const (match op with | .conjunction => ``And | .disjunction => ``Or) []) a) b

def evidence (op : Junction) (a b ha hb : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const
    (match op with | .conjunction => ``instDecidableAnd | .disjunction => ``instDecidableOr) []) a) b) ha) hb

end Junction

namespace GuardNegation

def condition : Nat → Lean.Expr → Lean.Expr
  | 0, expression => expression
  | n + 1, expression => .app (.const ``Not []) (condition n expression)

def evidence : Nat → Lean.Expr → Lean.Expr → Lean.Expr
  | 0, _, decision => decision
  | n + 1, expression, decision =>
      .app (.app (.const ``instDecidableNot []) (condition n expression)) (evidence n expression decision)

def denote : Nat → Bool → Bool
  | 0, value => value
  | n + 1, value => !(denote n value)

theorem condition_size (n : Nat) (expression : Lean.Expr) :
    sizeOf expression ≤ sizeOf (condition n expression) := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => simp only [condition]; simp_all; omega

end GuardNegation

end LeanExe.Source.Scalar
