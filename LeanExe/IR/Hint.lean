import Lean

namespace LeanExe.IR

/-- A compiler hint: the rule that produced `length` instructions of function
`func` in the decoded module, and the source term it translated.  `path` locates
the first instruction.  It lists instruction indices from the function body
inward; entering a `block` or `loop` continues with an index into its body, and
entering an `if` continues with 0 for the then-branch or 1 for the else-branch
and then an index.  Hints are untrusted: a wrong hint can only make a proof
harder to find. -/
structure Hint where
  func : Nat
  path : List Nat
  length : Nat
  rule : String
  source : String
  deriving Repr, Lean.ToExpr

structure Hints where
  /-- The name of each named local and its index: the source parameters, then
  the compiler's variables. -/
  locals : List (String × Nat)
  nodes : List Hint
  deriving Repr, Lean.ToExpr

end LeanExe.IR
