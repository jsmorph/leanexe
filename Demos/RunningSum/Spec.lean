import Demos.RunningSum.Program
import LeanExe.IR.Combinators

namespace Demos.RunningSum

def digitValue (byte : UInt64) : Nat := byte.toNat - 48

def digitsValue (digits : List UInt64) : Nat :=
  digits.foldl (fun value byte => 10 * value + digitValue byte) 0

def magnitude (digits : Array UInt64) : Nat := digitsValue digits.toList

def Decimal.value (number : Decimal) : Int :=
  if number.negative then -(magnitude number.digits : Int) else magnitude number.digits

def DecimalDigits (digits : Array UInt64) : Prop :=
  ∀ i, i < digits.size → 48 ≤ digits[i]!.toNat ∧ digits[i]!.toNat ≤ 57

def NormalDigits (digits : Array UInt64) : Prop :=
  DecimalDigits digits ∧ (digits.size = 0 ∨ digits[0]!.toNat ≠ 48)

def Decimal.Valid (number : Decimal) : Prop := NormalDigits number.digits

def Decimal.Fits (number : Decimal) : Prop := number.digits.size + 2 < UInt64.size

@[simp] theorem zero_value : zero.value = 0 := rfl

theorem zero_valid : zero.Valid := by
  simp [Decimal.Valid, NormalDigits, DecimalDigits, zero]

theorem zero_fits : zero.Fits := by
  change 2 < 18446744073709551616
  decide

end Demos.RunningSum
