import Library.Numerics.Arithmetic.MillerRabin.Compiled
import Verified.Master

namespace Library.Numerics.Arithmetic.MillerRabin

/-- The export `powMod`, called on words `x`, `n`, and `m`, returns `x ^ n % m` for `m ≠ 0` and
0 for `m = 0`. -/
theorem powMod_master :
    Verified.Master compiled.module compiled.tables "powMod" compiled.powMod.bound
      (fun _ => True)
      (fun (x : UInt64 × UInt64 × UInt64) y => y =
        if x.2.2 = 0 then 0 else UInt64.ofNat (x.1.toNat ^ x.2.1.toNat % x.2.2.toNat)) :=
  .of_trapFree (.ofA compiled.powMod.trapFree) nofun powMod_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => powMod_eq x.1 x.2.1 x.2.2

#print axioms powMod_master

/-- The export `test`, called on words `n` and `x`, returns 1 when `n` is odd, `n ≥ 3`, and `n`
is a strong probable prime to the base `x`, and 0 otherwise. -/
theorem test_master :
    Verified.Master compiled.module compiled.tables "test" compiled.test.bound (fun _ => True)
      (fun (x : UInt64 × UInt64) (y : UInt64) => y =
        if x.1.toNat % 2 = 1 ∧ 3 ≤ x.1.toNat ∧ StrongProbablePrime x.1.toNat x.2.toNat then 1
        else 0) :=
  .of_trapFree (.ofA compiled.test.trapFree) nofun test_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => test_eq x.1 x.2

#print axioms test_master

end Library.Numerics.Arithmetic.MillerRabin
