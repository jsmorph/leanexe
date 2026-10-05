import Mathlib.Data.Nat.Factors

/-! The specification of main's Demo 1, as its request states it: the number of prime factors of
a word, counted with multiplicity, which is 0 for 0 and 1. -/

namespace Project.PrimeFactors

def expected (n : UInt64) : UInt64 := UInt64.ofNat n.toNat.primeFactorsList.length

end Project.PrimeFactors
