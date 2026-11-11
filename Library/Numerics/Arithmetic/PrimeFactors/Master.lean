import Library.Numerics.Arithmetic.PrimeFactors.Compiled
import Verified.Master

namespace Library.Numerics.Arithmetic.PrimeFactors

/-- The export `compute`, called on a word `n`, returns the number of prime factors of `n`
counted with multiplicity, which is 0 for 0 and 1. -/
theorem compute_master :
    Verified.Master compiled.module compiled.tables "compute" compiled.compute.bound
      (fun _ => True)
      (fun (n : UInt64) y => y = UInt64.ofNat n.toNat.primeFactorsList.length) :=
  .of_trapFree (.ofA compiled.compute.trapFree) nofun compute_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ n _ _ => compute_eq n

#print axioms compute_master

end Library.Numerics.Arithmetic.PrimeFactors
