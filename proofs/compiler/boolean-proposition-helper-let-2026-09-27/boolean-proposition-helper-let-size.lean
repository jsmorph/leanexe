import LeanExe.Source.ScalarGuardLet
open LeanExe.Source.Scalar
#reduce guardOperandOverhead
#reduce sizeOf (Lean.Expr.app (.const ``UInt64.ofNat []) (.lit (.natVal 0)))
#reduce sizeOf (Lean.Expr.const ``True [])
#reduce sizeOf ("ite" : String) + sizeOf (.const ``Bool [] : Lean.Expr)
#reduce sizeOf ("dite" : String) + sizeOf (.const ``Bool [] : Lean.Expr)
#reduce sizeOf (Lean.Expr.const ``Decidable.decide [])
example : max guardOperandOverhead
    (sizeOf (Lean.Expr.app (.const ``UInt64.ofNat []) (.lit (.natVal 0))) -
      sizeOf (Lean.Expr.const ``True []) + 1) ≤
    sizeOf ("ite" : String) + sizeOf (.const ``Bool [] : Lean.Expr) := by decide
example : max guardOperandOverhead
    (sizeOf (Lean.Expr.app (.const ``UInt64.ofNat []) (.lit (.natVal 0))) -
      sizeOf (Lean.Expr.const ``True []) + 1) ≤
    sizeOf (Lean.Expr.const ``Decidable.decide []) := by decide
