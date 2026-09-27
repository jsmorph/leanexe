import LeanExe.Extract.ScalarExprCore
open LeanExe.Extract.Core
example (locals : List ScalarBinding) (source : Lean.Expr) : True := by
  fun_induction extractScalarExprWith locals source <;> trivial
#print extractScalarExprWith.induct
