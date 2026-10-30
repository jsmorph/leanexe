import Library.Numerics.Arithmetic.Gcd.Proof
import Verified.Reflect.Command

/-! The verified compiler's module of `gcd`.  The compiler translates the tail recursion into a
loop, and the generated `compiled.gcd.pure` states that function 2 computes `gcd` from every store
without a trap and keeps the store.  `gcd_call` composes it with `gcd_eq`. -/

namespace Library.Numerics.Arithmetic.Gcd

open Wasm LeanExe.Pipeline

verified_compile compiled := [gcd]

theorem gcd_export :
    ({ name := "gcd", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 2, the export `gcd`, called with the words `a` and `b` from any store, returns without
a trap the word of `Nat.gcd a.toNat b.toNat` and leaves the store unchanged. -/
theorem gcd_call (env : HostEnv Unit) (store : Store Unit) (a b : UInt64) :
    Runs false env compiled.module 2 store [.i64 b, .i64 a] fun final values =>
      final = store ∧ values = [.i64 (expected (a, b))] :=
  (compiled.gcd.pure env store (a, b)).mono fun _ values ⟨hs, hv⟩ => by
    refine ⟨hs, ?_⟩
    rw [← gcd_eq a b]
    simpa [Scalar.values] using congrArg List.reverse hv

#print axioms gcd_call

end Library.Numerics.Arithmetic.Gcd
