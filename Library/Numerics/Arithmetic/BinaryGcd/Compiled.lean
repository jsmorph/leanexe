import Library.Numerics.Arithmetic.BinaryGcd.Proof
import Verified.Reflect.Command
import Verified.Call

/-! The verified compiler's module of the binary GCD.  The compiler translates the tail recursions
of `removeTwos`, `commonTwos`, and `oddGcd` into loops.  `binaryGcd_callSpec` composes the
generated `compiled.binaryGcd.trapFree` with `binaryGcd_eq` as an instance of
`Verified.CallSpec`. -/

namespace Library.Numerics.Arithmetic.BinaryGcd

open Wasm LeanExe.Pipeline

verified_compile compiled := [removeTwos, commonTwos, oddGcd, binaryGcd]

theorem binaryGcd_export :
    ({ name := "binaryGcd", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 5, the export `binaryGcd`, called with the words `u` and `v` from a ready store with
room for `compiled.binaryGcd.bound (u, v)` bytes, returns without a trap the word of
`expected (u, v)`, the greatest common divisor, and leaves a ready store. -/
theorem binaryGcd_callSpec :
    Verified.CallSpec compiled.module compiled.tables 5 expected compiled.binaryGcd.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.binaryGcd.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ => binaryGcd_eq x.1 x.2

#print axioms binaryGcd_callSpec

end Library.Numerics.Arithmetic.BinaryGcd
