import Library.Numerics.Arithmetic.Sieve.Compiled
import Verified.Master

namespace Library.Numerics.Arithmetic.Sieve

/-- The export `primes`, called on a word `N`, returns the array of the primes below `N` in
increasing order. -/
theorem primes_master :
    Verified.Master compiled.module compiled.tables "primes" compiled.primes.bound
      (fun _ => True)
      (fun (N : UInt64) (y : Array UInt64) =>
        y = (((List.range N.toNat).filter fun p => decide (Nat.Prime p)).map UInt64.ofNat).toArray) :=
  .of_trapFree (.ofA compiled.primes.trapFree) nofun primes_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ N _ _ => primes_eq N

#print axioms primes_master

end Library.Numerics.Arithmetic.Sieve
