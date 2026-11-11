import Library.Numerics.Arithmetic.Gcd.Compiled
import Verified.Master

namespace Library.Numerics.Arithmetic.Gcd

/-- The export `gcd`, called on two words, returns the word of their greatest common divisor. -/
theorem gcd_master :
    Verified.Master compiled.module compiled.tables "gcd" compiled.gcd.bound (fun _ => True)
      (fun (x : UInt64 × UInt64) y => y = UInt64.ofNat (Nat.gcd x.1.toNat x.2.toNat)) :=
  .of_trapFree (.ofA compiled.gcd.trapFree) nofun gcd_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun x _ => gcd_eq x.1 x.2

#print axioms gcd_master

end Library.Numerics.Arithmetic.Gcd
