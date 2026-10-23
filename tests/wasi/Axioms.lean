import Verified.Bytes.Represent
import Verified.Bytes.Allocation
import Verified.Bytes.Get
import Verified.Bytes.CopyByte
import Verified.Bytes.Overlay
import Verified.Bytes.Copy
import Verified.Bytes.CopyOwned
import Verified.Bytes.Release
import Verified.Bytes.LiteralFrame
import LeanExe.Wasi.Prefix
import Verified.Examples.Bytes

open Lean Elab Command in
elab "check_wasi_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Prog.correctWith,
    ``Verified.Ty.Rep.step,
    ``Verified.wp_copyCode,
    ``Verified.wp_releaseCode,
    ``Verified.spec_bytesEmpty,
    ``Verified.spec_bytesSize,
    ``Verified.spec_bytesGet,
    ``Verified.Examples.Bytes.compiled.bytes,
    ``Verified.Examples.Bytes.compiled.identity.implements,
    ``Verified.Examples.Bytes.compiled.duplicate.implements,
    ``Verified.Examples.Bytes.compiled.choose.implements,
    ``Verified.Examples.Bytes.compiled.discard.implements,
    ``Verified.Examples.Bytes.compiled.swap.implements,
    ``Verified.Examples.Bytes.compiled.firstDuplicate.implements,
    ``Verified.Examples.Bytes.compiled.secondDuplicate.implements,
    ``Verified.Examples.Bytes.compiled.swappedFirst.implements,
    ``Verified.Examples.Bytes.compiled.emptyBuffer.implements,
    ``Verified.Examples.Bytes.compiled.readSize.implements,
    ``Verified.Examples.Bytes.compiled.readByte.implements,
    ``Verified.Examples.Bytes.compiled.ownedSize.implements,
    ``Verified.Examples.Bytes.compiled.ownedByte.implements,
    ``Verified.Examples.Bytes.compiled.lastByte.implements,
    ``Verified.Examples.Bytes.compiled.emptyRead.implements,
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
    ``Verified.Bytes.Allocated.write,
    ``Verified.Bytes.Allocated.write_step,
    ``Verified.Bytes.wp_store,
    ``Verified.Bytes.wp_copyByte,
    ``Verified.Bytes.overlay_zero,
    ``Verified.Bytes.overlay_all,
    ``Verified.Bytes.overlay_succ,
    ``Verified.Bytes.At.writesRange,
    ``Verified.Bytes.wp_copy,
    ``Verified.Bytes.wp_copyOwned,
    ``Verified.Bytes.Rep.release_step,
    ``Verified.Bytes.wp_release,
    ``Verified.Bytes.literalOffset_exists,
    ``Verified.Bytes.literalOffset_split,
    ``Verified.Bytes.literalOffset_bound,
    ``Verified.Bytes.literalOffset_byte,
    ``Verified.Bytes.LiteralPool.top_ge,
    ``Verified.Bytes.LiteralPool.top_lt,
    ``Verified.Bytes.LiteralPool.top_aligned,
    ``Verified.Bytes.LiteralPool.top_empty,
    ``Verified.Bytes.LiteralPool.segments_empty,
    ``Verified.Bytes.LiteralPool.Valid.frame,
    ``Verified.Bytes.LiteralPool.Valid.literal_bounds,
    ``Verified.Bytes.LiteralPool.Valid.literal,
    ``Verified.Bytes.LiteralPool.Static.empty,
    ``Verified.Bytes.LiteralPool.Static.literal,
    ``Verified.Bytes.LiteralPool.Static.step,
    ``LeanExe.Wasi.Action.bind_pure,
    ``LeanExe.Wasi.Action.bind_assoc,
    ``LeanExe.Wasi.exitStatus_toNat,
    ``LeanExe.Wasi.Exec.bind,
    ``LeanExe.Wasi.Exec.bind_iff,
    ``LeanExe.Wasi.resumeLoop_bind,
    ``LeanExe.Wasi.Exec.resumeLoop_iff,
    ``LeanExe.Wasi.Prefix.complete,
    ``LeanExe.Wasi.Prefix.exited_eq,
    ``LeanExe.Wasi.Exec.returned_prefix,
    ``LeanExe.Wasi.Prefix.bind_after,
    ``LeanExe.Wasi.readSome_overflow,
    ``LeanExe.Wasi.loop_zero,
    ``LeanExe.Wasi.Host.read_zero]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI axiom check passed for {theorems.size} theorems"

check_wasi_axioms
