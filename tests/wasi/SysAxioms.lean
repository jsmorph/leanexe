import Verified.Examples.WasiSys

/-! The axiom audit of the flat calls: the marshalling theorems of `Command.sys`, the program
theorems with imported calls, the reflection equations of the typed calls, the resource rule of a
reported call, the host totality theorems for `hostSpecWith`, and the generated theorems of the flat
call example use only `propext`, `Classical.choice`, and `Quot.sound`. -/

open Lean Elab Command in
elab "check_wasi_sys_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.flatArgs_fit,
    ``Verified.Wasi.wp_sys_flat_with,
    ``Verified.Wasi.wp_sys_reported_with,
    ``Verified.Wasi.command_sys_spec_with,
    ``Verified.Wasi.cost_command_sys_spec_with,
    ``Verified.Wasi.Command.code_spec_with,
    ``Verified.Wasi.Command.cost_code_spec_with,
    ``Verified.Wasi.EffectProg.correctWith_with,
    ``Verified.Wasi.compileWith_initialStore_with,
    ``Verified.Wasi.compiled_native_start_run_with,
    ``Verified.Wasi.compiled_native_entry_run_with,
    ``Verified.Wasi.Reflect.clockTimeGet_eq,
    ``Verified.Wasi.Reflect.randomGet_eq,
    ``Verified.Wasi.Reflect.argsSizesGet_eq,
    ``Verified.Wasi.Reflect.args_eq,
    ``Verified.Wasi.Resource.reported_rule_observed,
    ``Verified.Wasi.OracleSys.sys_contract,
    ``LeanExe.Wasi.Host.TotalFor.satisfiableWith,
    ``LeanExe.Wasi.Host.Answers.of_satisfiesWith,
    ``Verified.Examples.WasiSys.command.main.related,
    ``Verified.Examples.WasiSys.command.ready,
    ``Verified.Examples.WasiSys.command.calls,
    ``Verified.Examples.WasiSys.command.initial,
    ``Verified.Examples.WasiSys.command.start,
    ``Verified.Examples.WasiSys.command.exported,
    ``Verified.Examples.WasiSys.command.total,
    ``Verified.Examples.WasiSys.command.validity,
    ``Verified.Examples.WasiSys.command.bytes]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI flat call axiom check passed for {theorems.size} theorems"

check_wasi_sys_axioms

#print axioms Verified.Wasi.cost_command_sys_spec_with
#print axioms Verified.Examples.WasiSys.command.total
#print axioms Verified.Examples.WasiSys.command.bytes
