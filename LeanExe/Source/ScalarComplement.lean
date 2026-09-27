import Lean

namespace LeanExe.Source.Scalar

/-- Exact native and standard overloaded UInt64 complement syntax. -/
inductive ComplementHead : Lean.Expr → Prop where
  | direct : ComplementHead (.const ``UInt64.complement [])
  | canonical : ComplementHead
      (.app (.app (.const ``Complement.complement [.zero]) (.const ``UInt64 []))
        (.const ``instComplementUInt64 []))

theorem ComplementHead.not_ofNat {operation : Lean.Expr} (head : ComplementHead operation) (number : Nat) :
    operation ≠ .app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) (.lit (.natVal number)) := by
  cases head <;> simp

end LeanExe.Source.Scalar
