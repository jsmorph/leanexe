import Library.Numerics.Arithmetic.BinaryGcd.Compiled
import Verified.Master

namespace Library.Numerics.Arithmetic.BinaryGcd

/-- The export `binaryGcd`, called on two words, returns the word of their greatest common
divisor. -/
theorem binaryGcd_master :
    Verified.Master compiled.module compiled.tables "binaryGcd" compiled.binaryGcd.bound
      (fun _ => True)
      (fun (x : UInt64 × UInt64) y => y = UInt64.ofNat (Nat.gcd x.1.toNat x.2.toNat)) :=
  .of_trapFree (.ofA compiled.binaryGcd.trapFree) nofun binaryGcd_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => binaryGcd_eq x.1 x.2

#print axioms binaryGcd_master

end Library.Numerics.Arithmetic.BinaryGcd
