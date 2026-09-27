import LeanExe.Source.ScalarBooleanSelected
open LeanExe.Source.Scalar
#reduce sizeOf (Lean.mkAppN (.const ``Decidable.decide []) #[.bvar 0, .bvar 0])
#reduce sizeOf (Lean.mkAppN (.const ``ite [.succ .zero]) #[BooleanType.boolean.expr, .bvar 0, .bvar 0, .bvar 0, .bvar 0])
#reduce sizeOf (Lean.Expr.const ``Bool [])
