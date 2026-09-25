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

/-- A guard tree retains each original scalar operand and its comparison syntax. -/
inductive Guard where
  | compare (op : Comparison) (left right : Lean.Expr)
  | junction (op : Junction) (left right : Guard)
  deriving Repr

namespace Guard

def operands : Guard → List Lean.Expr
  | .compare _ a b => [a, b]
  | .junction _ a b => a.operands ++ b.operands

def condition : Guard → Lean.Expr
  | .compare op a b => op.condition a b
  | .junction op a b => op.condition a.condition b.condition

def evidence : Guard → Lean.Expr
  | .compare op a b => op.evidence a b
  | .junction op a b => op.evidence a.condition b.condition a.evidence b.evidence

def denote (native : Lean.Expr → UInt64) : Guard → Bool
  | .compare op a b => op.denote (native a) (native b)
  | .junction op a b => op.denote (a.denote native) (b.denote native)

theorem operands_size (guard : Guard) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf guard.condition := by
  induction guard with
  | compare op a b =>
    simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
    have bounds := op.operands_size a b
    rcases member with rfl | rfl
    · exact bounds.1
    · exact bounds.2
  | junction op a b iha ihb =>
    simp only [operands, List.mem_append] at member
    cases op <;> simp only [condition, Junction.condition]
    all_goals rcases member with member | member
    all_goals first
      | (have h := iha member; simp_all; omega)
      | (have h := ihb member; simp_all; omega)

end Guard

/-- A non-atomic root keeps the existing comparison extraction path unchanged. -/
structure CompoundGuard where
  junction : Junction
  left : Guard
  right : Guard
  deriving Repr

namespace CompoundGuard

def tree (guard : CompoundGuard) : Guard := .junction guard.junction guard.left guard.right
abbrev operands (guard : CompoundGuard) : List Lean.Expr := guard.tree.operands
abbrev condition (guard : CompoundGuard) : Lean.Expr := guard.tree.condition
abbrev evidence (guard : CompoundGuard) : Lean.Expr := guard.tree.evidence
abbrev denote (guard : CompoundGuard) (native : Lean.Expr → UInt64) : Bool := guard.tree.denote native

def branch (guard : CompoundGuard) (type onTrue onFalse : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type)
    guard.condition) guard.evidence) onTrue) onFalse

end CompoundGuard
end LeanExe.Source.Scalar
