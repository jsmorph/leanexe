import Verified.Wasi.ScriptHostContracts
import Verified.Wasi.HostTotal

open Lean Elab Command in
elab "check_script_host_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.ScriptHost.Policy.validErrno,
    ``Verified.Wasi.ScriptHost.readStep_bound,
    ``Verified.Wasi.ScriptHost.writeStep_bound,
    ``Verified.Wasi.ScriptHost.exitStep_recorded,
    ``Verified.Wasi.ScriptHost.exitStep_rejected,
    ``Verified.Wasi.ScriptHost.oracle_sound,
    ``Verified.Wasi.ScriptHost.env_satisfies,
    ``Verified.Wasi.readBytes_value,
    ``Verified.Wasi.written_at,
    ``Verified.Wasi.at_count,
    ``Verified.Wasi.frame_host,
    ``Verified.Wasi.frame_payload,
    ``Verified.Wasi.frame_count,
    ``Verified.Wasi.OracleHost.readAfter_frame,
    ``Verified.Wasi.OracleHost.readAfter_at,
    ``Verified.Wasi.OracleHost.readAfter_source,
    ``Verified.Wasi.OracleHost.writeAfter_source,
    ``Verified.Wasi.OracleHost.read_contract,
    ``Verified.Wasi.OracleHost.write_contract,
    ``Verified.Wasi.OracleHost.exit_contract,
    ``Verified.Wasi.OracleHost.env_satisfies,
    ``LeanExe.Wasi.Host.Total.oracle_sound,
    ``LeanExe.Wasi.Host.Total.satisfiable,
    ``LeanExe.Wasi.Host.Total.answers,
    ``LeanExe.Wasi.Host.Answers.of_satisfies]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"Script host axiom check passed for {theorems.size} theorems"

check_script_host_axioms
