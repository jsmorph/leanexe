import LeanExe.Source.ScalarComplement
import LeanExe.Extract.ScalarPrimitive

namespace LeanExe.Extract.Core

/-- Bitwise complement uses the existing XOR instruction and the full word mask. -/
def lowerComplement (argument : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  ScalarPrimitive.lower .xor argument (.u64 18446744073709551615)

theorem lowerComplement_correct {argument : LeanExe.IR.Expr}
    {store after : LeanExe.IR.ScalarStore} {value : UInt64}
    (evaluated : argument.ScalarEval store value after) :
    (lowerComplement argument).ScalarEval store (UInt64.complement value) after := by
  have mask : UInt64.ofNat 18446744073709551615 = -1 := by decide
  have result := ScalarPrimitive.lower_correct .xor evaluated
    (LeanExe.IR.Expr.ScalarEval.const (s := after) (n := 18446744073709551615))
  change (lowerComplement argument).ScalarEval store
    (value ^^^ UInt64.ofNat 18446744073709551615) after at result
  rw [mask, UInt64.xor_neg_one] at result
  exact result

end LeanExe.Extract.Core
