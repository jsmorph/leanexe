import Verified.Wasi.ScriptHostContracts

open Lean Elab Command in
elab "check_script_host_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.ScriptHost.Policy.validErrno,
    ``Verified.Wasi.ScriptHost.readStep_bound,
    ``Verified.Wasi.ScriptHost.writeStep_bound,
    ``Verified.Wasi.ScriptHost.exitStep_recorded,
    ``Verified.Wasi.ScriptHost.exitStep_rejected,
    ``Verified.Wasi.ScriptHost.readBytes_value,
    ``Verified.Wasi.ScriptHost.written_at,
    ``Verified.Wasi.ScriptHost.at_count,
    ``Verified.Wasi.ScriptHost.frame_host,
    ``Verified.Wasi.ScriptHost.frame_payload,
    ``Verified.Wasi.ScriptHost.frame_count,
    ``Verified.Wasi.ScriptHost.readAfter_frame,
    ``Verified.Wasi.ScriptHost.readAfter_at,
    ``Verified.Wasi.ScriptHost.readAfter_source,
    ``Verified.Wasi.ScriptHost.writeAfter_source,
    ``Verified.Wasi.ScriptHost.read_contract,
    ``Verified.Wasi.ScriptHost.write_contract,
    ``Verified.Wasi.ScriptHost.exit_contract,
    ``Verified.Wasi.ScriptHost.env_satisfies]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"Script host axiom check passed for {theorems.size} theorems"

check_script_host_axioms
