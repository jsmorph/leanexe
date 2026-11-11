import Library.Numerics.Arithmetic.ModInverse.Compiled
import Verified.Master

namespace Library.Numerics.Arithmetic.ModInverse

/-- The export `modInverse`, called on words `a` and `m`, returns the inverse of `a` in `ZMod m`
as a number below `m` when `m ≥ 2` and `a` is coprime to `m`, and 0 otherwise. -/
theorem modInverse_master :
    Verified.Master compiled.module compiled.tables "modInverse" compiled.modInverse.bound
      (fun _ => True)
      (fun (x : UInt64 × UInt64) y => y =
        if 2 ≤ x.2.toNat ∧ Nat.Coprime x.1.toNat x.2.toNat then
          UInt64.ofNat ((x.1.toNat : ZMod x.2.toNat)⁻¹).val
        else 0) :=
  .of_trapFree (.ofA compiled.modInverse.trapFree) nofun modInverse_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => modInverse_eq x.1 x.2

#print axioms modInverse_master

end Library.Numerics.Arithmetic.ModInverse
