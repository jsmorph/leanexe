import Verified.Examples.WasiSysNested

/-! The axiom audit of the nested calls: the decoding of iovecs and subscriptions, the marshalling
and command theorems of the forms `iovecRead`, `iovecWrite`, and `poll`, the handle theorem over
flat arguments, the reflection equations of the seven typed functions of `fd_read`, `fd_pread`,
`fd_write`, `fd_pwrite`, and `poll_oneoff`, and the generated theorems of
`Verified.Examples.WasiSysNested`, its handle check and `handles` among them, use only `propext`,
`Classical.choice`, and `Quot.sound`. -/

open Lean Elab Command in
elab "check_sys_nested_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.Reflect.fdRead_eq,
    ``Verified.Wasi.Reflect.fdPread_eq,
    ``Verified.Wasi.Reflect.fdWrite_eq,
    ``Verified.Wasi.Reflect.fdPwrite_eq,
    ``Verified.Wasi.Reflect.pollClock_eq,
    ``Verified.Wasi.Reflect.pollRead_eq,
    ``Verified.Wasi.Reflect.pollWrite_eq,
    ``Verified.Wasi.OracleSys.decodeArgs_lower,
    ``Verified.Wasi.element_read,
    ``Verified.Wasi.subscription_fields_at,
    ``Verified.Wasi.readFields_args,
    ``Verified.Wasi.handleArgs_flatArgsWith,
    ``Verified.Wasi.wp_iovec_read_call_with,
    ``Verified.Wasi.wp_iovec_write_call_with,
    ``Verified.Wasi.wp_sys_iovec_read_accept_with,
    ``Verified.Wasi.wp_sys_iovec_read_with,
    ``Verified.Wasi.wp_sys_iovec_write_with,
    ``Verified.Wasi.wp_field_stores,
    ``Verified.Wasi.wp_fields_reject,
    ``Verified.Wasi.wp_poll_call_with,
    ``Verified.Wasi.wp_sys_poll_accept_with,
    ``Verified.Wasi.wp_sys_poll_with,
    ``Verified.Wasi.wp_sys_iovec_read_result_with,
    ``Verified.Wasi.wp_sys_iovec_write_result_with,
    ``Verified.Wasi.wp_sys_poll_result_with,
    ``Verified.Wasi.wp_sys_result_with,
    ``Verified.Wasi.command_sys_spec_with,
    ``Verified.Wasi.cost_command_sys_spec_with,
    ``Verified.Examples.WasiSysNested.command.main.related,
    ``Verified.Examples.WasiSysNested.command.ready,
    ``Verified.Examples.WasiSysNested.command.calls,
    ``Verified.Examples.WasiSysNested.command.initial,
    ``Verified.Examples.WasiSysNested.command.start,
    ``Verified.Examples.WasiSysNested.command.exported,
    ``Verified.Examples.WasiSysNested.command.total,
    ``Verified.Examples.WasiSysNested.command.validity,
    ``Verified.Examples.WasiSysNested.command.handlesChecked,
    ``Verified.Examples.WasiSysNested.command.handles,
    ``Verified.Wasi.Reflect.withOpen_rel,
    ``Verified.Examples.WasiSysNested.command.bytes]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI nested call axiom check passed for {theorems.size} theorems"

check_sys_nested_axioms

#print axioms Verified.Examples.WasiSysNested.command.total
#print axioms Verified.Examples.WasiSysNested.command.bytes
