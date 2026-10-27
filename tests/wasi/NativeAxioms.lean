import Verified.Wasi.NativeTotal

open Lean Elab Command in
elab "check_wasi_native_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.FunctionResult.toNative,
    ``Verified.Wasi.NativeFunctionResult.return_or_accepted_exit,
    ``Verified.Wasi.compiled_native_entry_run,
    ``Verified.Wasi.native_run_total]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI native axiom check passed for {theorems.size} theorems"

check_wasi_native_axioms
