import Mathlib.Data.Nat.GCD.Basic

/-! The specification: the greatest common divisor of two words, as Lean's `Nat.gcd` defines it
for natural numbers.  `Nat.gcd u 0 = u` and `Nat.gcd 0 v = v`, so the greatest common divisor of 0
and 0 is 0.  The result never exceeds the larger argument, so it fits in a word.  The specification
fixes the result and not the method: the program text alone shows that the module uses
subtraction, comparisons, parity tests, and shifts, and no division. -/

namespace Library.Numerics.Arithmetic.BinaryGcd

def expected (x : UInt64 × UInt64) : UInt64 := UInt64.ofNat (Nat.gcd x.1.toNat x.2.toNat)

end Library.Numerics.Arithmetic.BinaryGcd
