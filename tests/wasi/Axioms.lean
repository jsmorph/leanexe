import Verified.Bytes.Basic
import LeanExe.Wasi.Action

open Lean Elab Command in
elab "check_wasi_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``LeanExe.Bytes.size_toNat,
    ``LeanExe.Bytes.get_build,
    ``LeanExe.Bytes.get_toNat_lt,
    ``LeanExe.Pipeline.release_leaf_run,
    ``LeanExe.Pipeline.release_run,
    ``Verified.Bytes.Allocated.frame,
    ``Verified.Bytes.Allocated.get,
    ``Verified.Bytes.Allocated.release_run,
    ``LeanExe.Wasi.Action.bind_pure,
    ``LeanExe.Wasi.Action.bind_assoc,
    ``LeanExe.Wasi.exitStatus_toNat]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI axiom check passed for {theorems.size} theorems"

check_wasi_axioms
