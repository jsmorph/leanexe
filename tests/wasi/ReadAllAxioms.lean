import Verified.Examples.WasiReadAll

/-! The axiom audit of `readAll`: its source lemmas, the proofs of its code, its command rules,
and the generated theorems of the example module use only `propext`, `Classical.choice`, and
`Quot.sound`. -/

open Lean Elab Command in
elab "check_wasi_readall_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``LeanExe.Wasi.readAll_size,
    ``LeanExe.Wasi.ReadAllRest.initial,
    ``LeanExe.Wasi.ReadAllRest.next,
    ``Verified.Wasi.wp_readAll_loop,
    ``Verified.Wasi.wp_readAll,
    ``Verified.Wasi.wp_command_readAll,
    ``Verified.Wasi.command_readAll_spec,
    ``Verified.Wasi.cost_command_readAll_spec,
    ``Verified.Wasi.Command.code_spec,
    ``Verified.Wasi.Command.cost_code_spec,
    ``Verified.Wasi.Resource.Returns.readAll_size,
    ``Verified.Wasi.Resource.ResourcePrefix.erase,
    ``Verified.Wasi.Resource.ResourcePrefix.ofPrefix,
    ``Verified.Examples.WasiReadAll.command.main.related,
    ``Verified.Examples.WasiReadAll.command.start,
    ``Verified.Examples.WasiReadAll.command.total,
    ``Verified.Examples.WasiReadAll.command.validity,
    ``Verified.Examples.WasiReadAll.command.bytes]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI readAll axiom check passed for {theorems.size} theorems"

check_wasi_readall_axioms

#print axioms Verified.Wasi.wp_readAll
#print axioms Verified.Wasi.cost_command_readAll_spec
#print axioms Verified.Examples.WasiReadAll.command.total
#print axioms Verified.Examples.WasiReadAll.command.bytes
