import Verified.Bytes.Represent
import Verified.Bytes.Allocation
import Verified.Bytes.Get
import LeanExe.Wasi.Semantics

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
    ``Verified.Bytes.Rep.frame,
    ``Verified.Bytes.Rep.release_run,
    ``Verified.Bytes.Rep.step,
    ``Verified.Bytes.represented_length,
    ``Verified.Bytes.roots_regions,
    ``Verified.Bytes.block_snapshot,
    ``Verified.Bytes.allocationCost_eq,
    ``Verified.Bytes.allocationCost_ge,
    ``Verified.Bytes.wp_allocate,
    ``Verified.Bytes.wp_get,
    ``LeanExe.Wasi.Action.bind_pure,
    ``LeanExe.Wasi.Action.bind_assoc,
    ``LeanExe.Wasi.exitStatus_toNat,
    ``LeanExe.Wasi.Exec.bind,
    ``LeanExe.Wasi.readSome_overflow,
    ``LeanExe.Wasi.loop_zero,
    ``LeanExe.Wasi.Host.read_zero]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI axiom check passed for {theorems.size} theorems"

check_wasi_axioms
