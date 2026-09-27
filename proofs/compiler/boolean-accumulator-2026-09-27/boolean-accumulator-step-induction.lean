import LeanExe.Extract.ScalarBooleanStep
open LeanExe.Extract.Core
example (locals : List ScalarBinding) (source : Lean.Expr) : True := by
  fun_induction extractBooleanStepWith locals source <;> trivial
#print extractBooleanStepWith.induct
