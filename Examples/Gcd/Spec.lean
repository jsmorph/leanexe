import Mathlib.Data.Nat.GCD.Basic

/-! The specification behind the earlier system's Demo 6, for any second argument: the greatest
common divisor of two words, as Lean's `Nat.gcd` defines it for natural numbers. -/

namespace Examples.Gcd

def expected (x : UInt64 × UInt64) : UInt64 := UInt64.ofNat (Nat.gcd x.1.toNat x.2.toNat)

end Examples.Gcd
