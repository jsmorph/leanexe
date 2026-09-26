import Lean

namespace LeanExe.Source.Scalar

/-- Exact Nat type syntax, retaining elaborator metadata such as borrowedness. -/
inductive NaturalType : Lean.Expr → Prop where
  | natural : NaturalType (.const ``Nat [])
  | metadata (type : NaturalType expression) : NaturalType (.mdata data expression)

/-- Natural numeral syntax with the exact standard instance. This is a literal
fragment, independent of general runtime Nat arithmetic or local Nat values. -/
inductive NaturalLiteral (number : Nat) : Lean.Expr → Prop where
  | raw : NaturalLiteral number (.lit (.natVal number))
  | ofNat (type : NaturalType expression) : NaturalLiteral number
      (.app (.app (.app (.const ``OfNat.ofNat [.zero]) expression) (.lit (.natVal number)))
        (.app (.const ``instOfNatNat []) (.lit (.natVal number))))
  | metadata (value : NaturalLiteral number expression) : NaturalLiteral number (.mdata data expression)

theorem NaturalLiteral.raw_value {number found : Nat}
    (literal : NaturalLiteral number (.lit (.natVal found))) : number = found := by
  cases literal
  rfl

theorem NaturalLiteral.not_bvar {number expression} (literal : NaturalLiteral number expression) (index : Nat) :
    expression ≠ .bvar index := by
  cases literal <;> simp

end LeanExe.Source.Scalar
