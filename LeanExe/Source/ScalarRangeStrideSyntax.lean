import LeanExe.Source.ScalarRangeCount

namespace LeanExe.Source.Scalar.Range.Exit

/-- Literal strides are checked numerically. The original erased positivity
proof is retained verbatim; checked declarations may use generated proof names. -/
structure Stride where
  number : Nat
  positive : 0 < number
  fits : number < UInt64.size
  evidence : Lean.Expr

def Stride.source (stride : Stride) : Lean.Expr := Range.natLiteral stride.number

end LeanExe.Source.Scalar.Range.Exit
