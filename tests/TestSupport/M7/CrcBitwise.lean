import Library.Hashing.Crc.Bitwise.Compiled
import LeanExe.M7.Proof.Program
import LeanExe.M7.Proof.Bound

/-!
The bitwise CRC-32 of `Library.Hashing.Crc.Bitwise` on the Cortex-M7 back end.  The functions
that calls reach from `crc32Reg`, `crc32Byte`, and `crc32Word`, functions 2, 3, and 4 of
`compiled.module`, load, store, and access no global, so a step that calls them has no area, and
they use only the forms that the simulation covers.  `crcBitwise_functions` states that the
generator emits their code: `functionsOf` lays out the functions that calls reach from a function
as `genProgram` lays out those that calls reach from a step after `main`, and generates them with
the shared addresses of a program without an area.  `crcBitwise_static` gives `staticCost`, which
`crcBitwise_cost` turns through `costRun_le_staticCost` into a bound on the model's steps of every
call, and `crcBitwise_stack` gives the bytes of stack that a call uses.
-/

namespace TestSupport.M7.CrcBitwise

open Wasm LeanExe.M7 LeanExe.CallGraph Library.Hashing.Crc.Bitwise

/-- The code that the generator gives the functions that calls reach from function `k` of `m`,
laid out from `base` with the stack's limit `limit`, as `genProgram` lays out a step's functions,
or an error when one of them accesses the area. -/
def functionsOf (m : Module) (k : Nat) (base limit : UInt32) : GenM (List Instr) := do
  let fs ← (reachFrom m k).mapM (funcOf m)
  if fnsArea fs then throw "a function that accesses the area"
  let targets := callTargets m k
  let sig := sigIn targets fs
  genFunctions (tableOf targets (entriesFrom sig base fs))
    (progShared (endOf sig base fs) limit none) base fs

/-- The number of bytes of the generator's code for the functions that calls reach from function
`k` of `m`, or 0 when the generator rejects them. -/
def codeBytes (m : Module) (k : Nat) (base limit : UInt32) : Nat :=
  match functionsOf m k base limit with
  | .ok is => 2 * halfwordsOf is
  | .error _ => 0

/-- No function that calls reach from the three exports loads, stores, or accesses a global. -/
theorem crcBitwise_noArea :
    usesArea compiled.module 2 = false ∧ usesArea compiled.module 3 = false ∧
      usesArea compiled.module 4 = false := by
  decide +kernel

/-- The functions that calls reach from the three exports have the forms that the simulation
covers. -/
theorem crcBitwise_covered :
    reachCovered compiled.module 2 = true ∧ reachCovered compiled.module 3 = true ∧
      reachCovered compiled.module 4 = true := by
  decide +kernel

/-- The generator emits the code of the functions that calls reach from each export, at the base
of the board's `main` and with DTCM's base as the stack's limit, in the number of bytes given. -/
theorem crcBitwise_functions :
    codeBytes compiled.module 2 0x002003A8 0x20000000 = 2316 ∧
      codeBytes compiled.module 3 0x002003A8 0x20000000 = 2612 ∧
      codeBytes compiled.module 4 0x002003A8 0x20000000 = 5528 := by
  decide +kernel

/-- The static bound on the model's steps of every call of each export. -/
theorem crcBitwise_static :
    staticCost compiled.module 2 = some 579 ∧ staticCost compiled.module 3 = some 653 ∧
      staticCost compiled.module 4 = some 5363 := by
  decide +kernel

/-- The bytes of stack that a call of each export uses, with the generator's frames. -/
theorem crcBitwise_stack :
    stackBound compiled.module 2 = 96 ∧ stackBound compiled.module 3 = 136 ∧
      stackBound compiled.module 4 = 224 := by
  decide +kernel

/-- Every run of a call of `crc32Byte` takes at most 653 steps of the model, and every run of a
call of `crc32Word` at most 5,363, at every fuel, store, and argument list. -/
theorem crcBitwise_cost {α : Type} (F : Nat) (st : Store α) (vs : List Value) (env : HostEnv α) :
    costRun F compiled.module 3 st vs env ≤ 653 ∧
      costRun F compiled.module 4 st vs env ≤ 5363 :=
  ⟨costRun_le_staticCost rfl crcBitwise_static.2.1 F st vs,
    costRun_le_staticCost rfl crcBitwise_static.2.2 F st vs⟩

end TestSupport.M7.CrcBitwise
