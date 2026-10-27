import Verified.Wasi.PureTransportSpecs
import Verified.Wasi.RelocationForms
import Verified.Wasi.ModuleTransport
import Verified.Wasi.ModuleInitial
import Verified.Wasi.PurePrefix

open Lean Elab Command in
elab "check_transport_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.PureTransport.erase_restore,
    ``Verified.Wasi.PureTransport.restore_erase,
    ``Verified.Wasi.PureTransport.run_frame,
    ``Verified.Wasi.Relocation.function_shape,
    ``Verified.Wasi.Relocation.program_form,
    ``Verified.Wasi.PureTransport.transport_fuel,
    ``Verified.Wasi.PureTransport.code_transport,
    ``Verified.Wasi.PureTransport.entry_transport,
    ``Verified.Wasi.PureTransport.entry_keepsWorld,
    ``Verified.Wasi.PureTransport.runs_transport,
    ``Verified.Wasi.PureTransport.terminatesWith_transport,
    ``Verified.Wasi.PureTransport.entry_trap_world,
    ``Verified.Wasi.PureTransport.wp_transport,
    ``Verified.Wasi.Module.layout,
    ``Verified.Wasi.Module.shape,
    ``Verified.Wasi.Module.initialStore_eq,
    ``Verified.Wasi.Module.run_pure,
    ``Verified.Wasi.Module.runs_pure,
    ``Verified.Wasi.Module.terminatesWith_pure,
    ``Wasm.exec_append_match,
    ``Wasm.wp_append,
    ``Verified.Wasi.PureTransport.wp_prefix]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"Transport axiom check passed for {theorems.size} theorems"

check_transport_axioms
