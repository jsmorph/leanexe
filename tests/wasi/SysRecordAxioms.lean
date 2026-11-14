import Verified.Examples.WasiSysRecords

/-! The axiom audit of the record calls: the marshalling and command theorems of the record form,
the reflection equations of the four record calls, and the generated theorems of
`Verified.Examples.WasiSysRecords` use only `propext`, `Classical.choice`, and `Quot.sound`. -/

open Lean Elab Command in
elab "check_sys_record_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.Reflect.fdFdstatGet_eq,
    ``Verified.Wasi.Reflect.fdFilestatGet_eq,
    ``Verified.Wasi.Reflect.fdPrestatGet_eq,
    ``Verified.Wasi.Reflect.pathFilestatGet_eq,
    ``Verified.Wasi.wp_sys_record_call_with,
    ``Verified.Wasi.wp_field_load,
    ``Verified.Wasi.wp_record_loads,
    ``Verified.Wasi.wp_sys_record_accept_with,
    ``Verified.Wasi.wp_sys_record_with,
    ``Verified.Wasi.wp_sys_record_result_with,
    ``Verified.Wasi.wp_sys_result_with,
    ``Verified.Wasi.command_sys_spec_with,
    ``Verified.Wasi.cost_command_sys_spec_with,
    ``Verified.Examples.WasiSysRecords.command.main.related,
    ``Verified.Examples.WasiSysRecords.command.ready,
    ``Verified.Examples.WasiSysRecords.command.calls,
    ``Verified.Examples.WasiSysRecords.command.initial,
    ``Verified.Examples.WasiSysRecords.command.start,
    ``Verified.Examples.WasiSysRecords.command.exported,
    ``Verified.Examples.WasiSysRecords.command.total,
    ``Verified.Examples.WasiSysRecords.command.validity,
    ``Verified.Examples.WasiSysRecords.command.bytes]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI record call axiom check passed for {theorems.size} theorems"

check_sys_record_axioms

#print axioms Verified.Examples.WasiSysRecords.command.total
#print axioms Verified.Examples.WasiSysRecords.command.bytes
