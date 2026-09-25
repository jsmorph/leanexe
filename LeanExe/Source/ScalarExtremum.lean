import LeanExe.Source.ScalarComparison

namespace LeanExe.Source.Scalar

/-- The canonical UInt64 Min/Max instances, with their native results. -/
inductive Extremum where
  | minimum | maximum
  deriving DecidableEq, Repr

namespace Extremum

def denote : Extremum → UInt64 → UInt64 → UInt64
  | .minimum => min
  | .maximum => max

def head (op : Extremum) : Lean.Expr :=
  .app (.app (.const (match op with | .minimum => ``Min.min | .maximum => ``Max.max) [.zero])
    (.const ``UInt64 []))
    (.const (match op with | .minimum => ``instMinUInt64 | .maximum => ``instMaxUInt64) [])

def expr (op : Extremum) (a b : Lean.Expr) : Lean.Expr := .app (.app op.head a) b

end Extremum
end LeanExe.Source.Scalar
