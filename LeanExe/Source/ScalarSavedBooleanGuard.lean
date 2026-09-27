import LeanExe.Source.ScalarBooleanGuard

namespace LeanExe.Source.Scalar

/-- A Boolean leaf beyond the closed comparison grammar, used as a proposition. -/
structure SavedBooleanGuard where
  value : Lean.Expr
  extended : ∀ guard : BooleanGuard, value ≠ guard.expr
  propNegations : Nat := 0
  deriving Repr

namespace SavedBooleanGuard

def expr (guard : SavedBooleanGuard) : Lean.Expr := guard.value

def operand (guard : SavedBooleanGuard) : Lean.Expr :=
  .app (.const ``Bool.toUInt64 []) guard.expr

def condition (guard : SavedBooleanGuard) : Lean.Expr :=
  GuardNegation.condition guard.propNegations
    (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) guard.expr) (.const ``Bool.true []))

def evidence (guard : SavedBooleanGuard) : Lean.Expr :=
  GuardNegation.evidence guard.propNegations
    (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) guard.expr) (.const ``Bool.true []))
    (.app (.app (.const ``instDecidableEqBool []) guard.expr) (.const ``Bool.true []))

def denote (guard : SavedBooleanGuard) (native : Lean.Expr → UInt64) : Bool :=
  GuardNegation.denote guard.propNegations (native guard.operand == 1)

def negate (guard : SavedBooleanGuard) : SavedBooleanGuard :=
  { guard with propNegations := guard.propNegations + 1 }

theorem negate_condition (guard : SavedBooleanGuard) :
    guard.negate.condition = .app (.const ``Not []) guard.condition := rfl

theorem operand_size (guard : SavedBooleanGuard) :
    sizeOf guard.operand < sizeOf guard.condition := by
  apply Nat.lt_of_lt_of_le _ (GuardNegation.condition_size guard.propNegations _)
  have names : sizeOf ("toUInt64" : String) ≤
      sizeOf ("Bool" : String) + sizeOf ("Eq" : String) + sizeOf ("true" : String) := by decide
  simp [operand]; omega

end SavedBooleanGuard
end LeanExe.Source.Scalar
