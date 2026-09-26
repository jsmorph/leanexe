import LeanExe.Extract.ScalarBooleanPredicateEquality
open LeanExe.Source.Scalar
#reduce sizeOf "ite"
#reduce sizeOf "Bool"
#reduce sizeOf "Decidable"
#reduce sizeOf "decide"
#reduce sizeOf (Lean.Expr.bvar 0)
#reduce sizeOf (BooleanLocal.choice 0 false (.var 0 0) (.var 0 0) (.var 0 0) (.var 0 0)).expr
#reduce sizeOf (BooleanLocal.relationDecision 0 false (.var 0 0) (.var 0 0)).expr
