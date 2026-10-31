import Library.Numerics.Arithmetic.MillerRabin.Proof
import Verified.Reflect.Command
import Verified.Call

/-! The verified compiler's module of modular exponentiation and the strong probable-prime test.
The program allocates nothing, so the generated `trapFree` theorems exclude a trap without a
premise on free memory.  `powMod_callSpec` and `test_callSpec` compose them with `powMod_eq` and
`test_eq`. -/

namespace Library.Numerics.Arithmetic.MillerRabin

open Wasm LeanExe.Pipeline

verified_compile compiled := [addMod, mulMod, powMod, twos, test]

theorem powMod_export :
    ({ name := "powMod", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem test_export :
    ({ name := "test", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- From a ready store with room for `compiled.powMod.bound x` bytes, function 4, the export
`powMod`, returns `powModSpec x` without a trap and leaves a ready store. -/
theorem powMod_callSpec :
    Verified.CallSpec compiled.module compiled.tables 4 powModSpec compiled.powMod.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.powMod.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ => powMod_eq x.1 x.2.1 x.2.2

/-- From a ready store with room for `compiled.test.bound x` bytes, function 6, the export `test`,
returns `testSpec x` without a trap and leaves a ready store. -/
theorem test_callSpec :
    Verified.CallSpec compiled.module compiled.tables 6 testSpec compiled.test.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.test.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ => test_eq x.1 x.2

#print axioms powMod_callSpec
#print axioms test_callSpec
#print axioms test_prime

end Library.Numerics.Arithmetic.MillerRabin
