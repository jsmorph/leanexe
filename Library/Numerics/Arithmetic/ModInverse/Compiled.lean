import Library.Numerics.Arithmetic.ModInverse.Proof
import Verified.Reflect.Command
import Verified.Call

/-! The verified compiler's module of the modular inverse.  The compiler translates the tail
recursion of `euclid` into a loop.  `modInverse_callSpec` composes the generated
`compiled.modInverse.trapFree` with `modInverse_eq` as an instance of `Verified.CallSpec`. -/

namespace Library.Numerics.Arithmetic.ModInverse

open Wasm LeanExe.Pipeline

verified_compile compiled := [euclid, modInverse]

theorem modInverse_export :
    ({ name := "modInverse", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 3, the export `modInverse`, called with the words `a` and `m` from a ready store with
room for `compiled.modInverse.bound (a, m)` bytes, returns without a trap the word of
`expected (a, m)`, the inverse of `a` modulo `m` or 0, and leaves a ready store. -/
theorem modInverse_callSpec :
    Verified.CallSpec compiled.module compiled.tables 3 expected compiled.modInverse.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.modInverse.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ => modInverse_eq x.1 x.2

#print axioms modInverse_callSpec

end Library.Numerics.Arithmetic.ModInverse
