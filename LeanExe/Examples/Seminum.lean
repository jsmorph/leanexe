import LeanExe.Lib.NumberTheory.Gcd
import LeanExe.Lib.NumberTheory.BinaryGcd
import LeanExe.Lib.Polynomial.Horner
import LeanExe.Lib.Transcendental.Exp

namespace LeanExe.Examples.Seminum

structure ScalarResult where
  status : UInt64 := 0
  value : UInt64 := 0
  deriving Repr

structure FractionResult where
  status : UInt64 := 0
  numerator : UInt64 := 0
  denominator : UInt64 := 0
  deriving Repr

def reduced (numerator denominator divisor : UInt64) : FractionResult :=
  if denominator == 0 then { status := 1 }
  else
    { numerator := numerator / divisor, denominator := denominator / divisor }

def fraction (numerator denominator : UInt64) : FractionResult :=
  reduced numerator denominator (Lib.NumberTheory.gcd numerator denominator)

def fractionBinary (numerator denominator : UInt64) : FractionResult :=
  reduced numerator denominator (Lib.NumberTheory.gcdBinary numerator denominator)

def polynomial (x : UInt64) (coefficients : Array UInt64) : ScalarResult :=
  match Lib.Polynomial.eval coefficients x with
  | some value => { value }
  | none => { status := 2 }

def ratio (x : UInt64) (numerator denominator : Array UInt64) : FractionResult :=
  match Lib.Polynomial.eval numerator x with
  | none => { status := 2 }
  | some n =>
    match Lib.Polynomial.eval denominator x with
    | none => { status := 2 }
    | some d => fraction n d

def exponential (bits : UInt64) : ScalarResult :=
  match Lib.Transcendental.expTaylor6 bits with
  | some value => { value }
  | none => { status := 3 }

def decay (timeBits : UInt64) : ScalarResult :=
  if timeBits <= 0x3FF0000000000000 || timeBits == 0x8000000000000000 then
    exponential (timeBits ^^^ 0x8000000000000000)
  else { status := 4 }

end LeanExe.Examples.Seminum
