import Library.Numerics.Arithmetic.PrimeFactors.Proof
import Verified.Reflect.Command

/-! The verified compiler's module of `countFactors` and `compute`.  The reflector reads the
condition `remaining ≤ 1 ∨ divisor ≤ 1` as the disjunction of its two decisions and compiles the
tail recursion into a loop, and the generated `compiled.compute.pure` states that function 3
computes `compute` from every store without a trap and keeps the store.  `primeFactors_call`
composes it with `compute_eq`. -/

namespace Library.Numerics.Arithmetic.PrimeFactors

open Wasm LeanExe.Pipeline

verified_compile compiled := [countFactors, compute]

theorem compute_export :
    ({ name := "compute", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 3, the export `compute`, called with the word `n` from any store, returns without a
trap the number of prime factors of `n` counted with multiplicity, 0 for 0 and 1, and leaves the
store unchanged. -/
theorem primeFactors_call (env : HostEnv Unit) (store : Store Unit) (n : UInt64) :
    Runs false env compiled.module 3 store [.i64 n] fun final values =>
      final = store ∧ values = [.i64 (expected n)] :=
  (compiled.compute.pure env store n).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, ?_⟩
    rw [← compute_eq n]
    simpa [Scalar.values] using congrArg List.reverse hv

#print axioms primeFactors_call

end Library.Numerics.Arithmetic.PrimeFactors
