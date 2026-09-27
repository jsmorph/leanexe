import LeanExe.Extract.ScalarFunc
open LeanExe.Source.Scalar
#reduce (sizeOf ("True" : String), sizeOf ("Eq" : String), sizeOf ("Ne" : String),
  sizeOf ("Bool" : String), sizeOf ("toUInt64" : String), sizeOf ("ite" : String),
  guardOperandOverhead)
#reduce (sizeOf (Lean.Expr.app (.const ``Bool.toUInt64 []) (.bvar 0)),
  sizeOf (Lean.Expr.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) (.bvar 0)) (.bvar 0)),
  sizeOf (Lean.Expr.app (.const ``Bool.toUInt64 []) (.bvar 0)) <
    sizeOf (Lean.Expr.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) (.bvar 0)) (.bvar 0)) + guardOperandOverhead)
