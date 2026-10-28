import Verified.Wasi.ProcessLoop
import Verified.Wasi.ProcessMemory
import Verified.Wasi.ProcessIteration
import Verified.Wasi.ProcessFacts
import Verified.Wasi.ProcessCorrect
import Verified.Wasi.ProcessNative
import Verified.Wasi.ProcessTermination
import LeanExe.Wasi.ProcessRelated
import Verified.Wasi.Stack

open Lean Elab Command in
elab "check_process_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Wasm.wp.pwp, ``Wasm.pwp_append, ``Wasm.pwp_loop,
    ``LeanExe.Wasi.Process.Exec.exited_marker,
    ``LeanExe.Wasi.Process.Progress.finish,
    ``LeanExe.Wasi.Process.Progress.done,
    ``Verified.Wasi.pwp_process_loop, ``Verified.Wasi.pwp_process_block,
    ``Verified.Wasi.ProcessMemory.called, ``Verified.Wasi.ProcessMemory.compacted,
    ``Verified.Wasi.ProcessMemory.state, ``Verified.Wasi.wp_compactCode,
    ``Verified.Wasi.wp_process_compact, ``Verified.Wasi.wp_process_store_compact,
    ``Verified.Wasi.wp_process_iteration, ``Verified.Wasi.ProcessStored.status,
    ``Verified.Wasi.compileProcess_initialStore,
    ``Verified.Wasi.pwp_process_entry_body,
    ``Verified.Wasi.process_entry_run,
    ``Verified.Wasi.compiled_process_body,
    ``Verified.Wasi.compiled_process_run,
    ``Verified.Wasi.ProcessEntryRunResult.transport_back,
    ``Verified.Wasi.wp_process_loop_ranked,
    ``Verified.Wasi.wp_process_block_ranked,
    ``LeanExe.Wasi.Process.Rel.exec_back,
    ``LeanExe.Wasi.Process.Rel.continue_back,
    ``LeanExe.Wasi.Process.Rel.pending_back,
    ``Verified.Wasi.EffectProg.correctIn,
    ``Verified.Wasi.stackBound_effects, ``Verified.Wasi.stackBound_path]
  for declaration in declarations do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"Process axiom check passed for {declarations.size} theorems"

check_process_axioms
