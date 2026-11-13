import Verified.Examples.WasiSysEnviron

/-! The axiom audit of the environment example: the reflection equation of `environ` and the
generated theorems of `Verified.Examples.WasiSysEnviron` use only `propext`, `Classical.choice`,
and `Quot.sound`. -/

open Lean Elab Command in
elab "check_sys_environ_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.Reflect.environ_eq,
    ``Verified.Examples.WasiSysEnviron.command.main.related,
    ``Verified.Examples.WasiSysEnviron.command.ready,
    ``Verified.Examples.WasiSysEnviron.command.calls,
    ``Verified.Examples.WasiSysEnviron.command.initial,
    ``Verified.Examples.WasiSysEnviron.command.start,
    ``Verified.Examples.WasiSysEnviron.command.exported,
    ``Verified.Examples.WasiSysEnviron.command.total,
    ``Verified.Examples.WasiSysEnviron.command.validity,
    ``Verified.Examples.WasiSysEnviron.command.handles,
    ``Verified.Examples.WasiSysEnviron.command.bytes]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI environment example axiom check passed for {theorems.size} theorems"

check_sys_environ_axioms
