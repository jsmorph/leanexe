import Lean

namespace Project.IR

/-- A compiler hint: the rule that produced instructions `start` to `stop - 1`
of function `func` in the decoded module, and the source term it translated.
Hints are untrusted: a wrong hint can only make a proof harder to find. -/
structure Hint where
  func : Nat
  start : Nat
  stop : Nat
  rule : String
  source : String
  deriving Repr, Lean.ToExpr

structure Hints where
  /-- Each source parameter's name and the local that holds it. -/
  params : List (String × Nat)
  nodes : List Hint
  deriving Repr, Lean.ToExpr

end Project.IR
