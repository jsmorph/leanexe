import Verified.Examples.WasiSysPrestat

/-! The axiom audit of the prestat example: the reflection equations of its typed functions, the
handle check's lemmas for the binding of `Handle.preopened` under `letPair`, and the generated
theorems of `Verified.Examples.WasiSysPrestat`, its handle check and `handles` among them, use
only `propext`, `Classical.choice`, and `Quot.sound`. -/

open Lean Elab Command in
elab "check_sys_prestat_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.Reflect.fdPrestatGet_eq,
    ``Verified.Wasi.Reflect.fdPrestatDirName_eq,
    ``Verified.Wasi.Reflect.fdWrite_eq,
    ``Verified.Wasi.Reflect.fdPread_eq,
    ``Verified.Wasi.Reflect.pathUnlinkFile_eq,
    ``Verified.Wasi.Reflect.withOpen_rel,
    ``Verified.Wasi.Reflect.withOpen_rel_mk,
    ``Verified.Expr.isPreopened_denote,
    ``Verified.Wasi.Command.preopened_handles,
    ``Verified.Examples.WasiSysPrestat.command.main.related,
    ``Verified.Examples.WasiSysPrestat.command.ready,
    ``Verified.Examples.WasiSysPrestat.command.calls,
    ``Verified.Examples.WasiSysPrestat.command.initial,
    ``Verified.Examples.WasiSysPrestat.command.start,
    ``Verified.Examples.WasiSysPrestat.command.exported,
    ``Verified.Examples.WasiSysPrestat.command.total,
    ``Verified.Examples.WasiSysPrestat.command.validity,
    ``Verified.Examples.WasiSysPrestat.command.handlesChecked,
    ``Verified.Examples.WasiSysPrestat.command.handles,
    ``Verified.Examples.WasiSysPrestat.command.bytes]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI prestat example axiom check passed for {theorems.size} theorems"

check_sys_prestat_axioms

#print axioms Verified.Examples.WasiSysPrestat.command.total
#print axioms Verified.Examples.WasiSysPrestat.command.bytes
