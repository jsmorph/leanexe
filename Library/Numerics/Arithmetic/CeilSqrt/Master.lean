import Library.Numerics.Arithmetic.CeilSqrt.Compiled
import Library.Numerics.Arithmetic.CeilSqrt.Proof
import Verified.Master

namespace Library.Numerics.Arithmetic.CeilSqrt

theorem ceilSqrt_export :
    ({ name := "ceilSqrt", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The export `ceilSqrt`, called on a word `n ≤ 2 ^ 32`, returns the least `r` with
`n ≤ r * r`, which is at most `2 ^ 16`. -/
theorem ceilSqrt_master :
    Verified.Master compiled.module compiled.tables "ceilSqrt" compiled.ceilSqrt.bound
      (fun n : UInt64 => n.toNat ≤ 2 ^ 32)
      (fun n (r : UInt64) => r.toNat ≤ 2 ^ 16 ∧ n.toNat ≤ r.toNat * r.toNat ∧
        ∀ j, j < r.toNat → j * j < n.toNat) :=
  .of_trapFree (.ofA compiled.ceilSqrt.trapFree) nofun ceilSqrt_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ n _ hn => Sqrt.ceilSqrt_correct n hn

#print axioms ceilSqrt_master

end Library.Numerics.Arithmetic.CeilSqrt
