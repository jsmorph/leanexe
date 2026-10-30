import Library.Numerics.Arithmetic.Gcd.Proof
import Verified.Reflect.Command
import Verified.Call

/-! The verified compiler's module of `gcd`.  The compiler translates the tail recursion into a
loop, and the generated `compiled.gcd.pure` states that function 2 computes `gcd` from every store
without a trap and keeps the store.  `gcd_call` composes it with `gcd_eq`.  `gcd_callSpec` states the
call from a ready store as an instance of `Verified.CallSpec`, from `compiled.gcd.trapFree`. -/

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

/-- `Verified.CallSpec` for function 2 and `expected`, with the generated bound as the room: from a
ready store in which `top` can rise by `compiled.gcd.bound (a, b)` bytes, the call returns the word
of `expected (a, b)` and leaves a ready store.  `gcd_call` states more for this function: the call
succeeds from every store and leaves it unchanged. -/
theorem gcd_callSpec :
    Verified.CallSpec compiled.module compiled.tables 2 expected compiled.gcd.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.gcd.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ => gcd_eq x.1 x.2

#print axioms gcd_call
#print axioms gcd_callSpec

end Library.Numerics.Arithmetic.Gcd
