import Verified.Examples.WasiSysInputs

/-! The axiom audit of the flat calls with inputs: the marshalling and command theorems with
inputs, the reflection equations of the calls of `Verified.Examples.WasiSysInputs`, and the
generated theorems of that example use only `propext`, `Classical.choice`, and `Quot.sound`. -/

open Lean Elab Command in
elab "check_sys_inputs_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.Reflect.pathCreateDirectory_eq,
    ``Verified.Wasi.Reflect.pathRemoveDirectory_eq,
    ``Verified.Wasi.Reflect.environ_eq,
    ``Verified.Wasi.wp_sys_result_with,
    ``Verified.Wasi.command_sys_spec_with,
    ``Verified.Wasi.cost_command_sys_spec_with,
    ``Verified.Wasi.wp_sys_flat_inputs_with,
    ``Verified.Examples.WasiSysInputs.command.main.related,
    ``Verified.Examples.WasiSysInputs.command.ready,
    ``Verified.Examples.WasiSysInputs.command.calls,
    ``Verified.Examples.WasiSysInputs.command.initial,
    ``Verified.Examples.WasiSysInputs.command.start,
    ``Verified.Examples.WasiSysInputs.command.exported,
    ``Verified.Examples.WasiSysInputs.command.total,
    ``Verified.Examples.WasiSysInputs.command.validity,
    ``Verified.Examples.WasiSysInputs.command.bytes]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI input call axiom check passed for {theorems.size} theorems"

check_sys_inputs_axioms

#print axioms Verified.Examples.WasiSysInputs.command.total
#print axioms Verified.Examples.WasiSysInputs.command.bytes
