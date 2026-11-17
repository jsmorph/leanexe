import TestSupport.A64.WasiElf
import Verified.Examples.WasiSysNative
import LeanExe.A64.File

/-!
The theorems of the Linux executable that `a64-wasi emit` writes for the flat call example of
`Verified.Examples.WasiSys`, a WASI command that writes its arguments, their count and size, the
readings of clocks 0 and 1, and 16 random bytes.  `tests/linux/a64-wasi.sh` elaborates this file
in the directory of the executable, so `file_nat%` and `file_size%` read sys.elf, and no build
target includes it.  The kernel evaluates `genWasiElf` on the command's module, the index of
`_start`, the stack's room, and the cap, and checks that the executable's bytes are the file's
(`sys_elf_file`).  `sys_elf_segments` states the two program headers that `elfSegments` reads
from the file, `sys_elf_layout` that they are those of the generator's layout, `sys_elf_entry`
that the file's entry is the prefix `wasiEntry`, and `sys_elf_room` that the stack's room holds
the module's stack bound.

`sys_elf` holds for every reply sequence.  From a process whose memory holds the file as Linux's
loader places it, with the arguments `args` and the environment `environ` on Linux's initial stack
at SP, the program counter at the entry, and no event in the trace, the process reaches `SVC #0`
with X8 at 94, `exit_group`, with the UART's state as it was.  Its trace holds the layer events
`ls`, the images of the WASI events `T` of a run of the command's action under `linuxHost` with the
launch `⟨args, environ, false⟩`, so the arguments that the run's `args_sizes_get` and `args_get`
report are those of `args`.  Each event of `ls` holds its reply and writes within the cap's linear
memory or into the timespec, and the writes of descriptor 1 in `ls` took the bytes that the
`fd_write` events of `T` to standard output committed.  `T` is the trace of an `Exec` run that ends
at an accepted exit, whose status X0 holds, at an exit that the shim rejects, with X0 at 1, or at a
trap of the shim, with X0 at 2, or of a `Prefix` run of the action, with X0 at 2.
-/

namespace TestSupport.A64.ImageFilesWasiSys

open LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim Verified.ShimA64
  Verified.Examples.WasiSys TestSupport.A64.WasiElf

def sysElfBytes : Nat := file_nat% "sys.elf"
def sysElfSize : Nat := file_size% "sys.elf"

/-- The executable's layout. -/
def sysLayout : ElfLayout := wasiLayout command.module sysStart wasiRoom wasiCap

/-- The shim's layout of the executable. -/
def sysShimLayout : ShimLayout := wasiShimLayout command.module sysStart wasiRoom wasiCap

set_option maxRecDepth 100000

theorem sys_elf_file : bytesOk (genWasiElf command.module sysStart wasiRoom wasiCap)
    sysElfBytes sysElfSize = true := by decide +kernel

theorem sys_elf_segments : elfSegments (byteAt sysElfBytes) =
    [⟨1, 5, 0, 0x400000, 20560, 20560⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem sys_elf_layout : elfSegmentsOf sysLayout =
    [⟨1, 5, 0, 0x400000, 20560, 20560⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem sys_elf_entry : elfEntryOf (byteAt sysElfBytes) = wasiEntry.toNat := by
  decide +kernel

theorem sys_elf_room : wasiStackBound command.module sysStart ≤ wasiRoom.toNat := by
  decide +kernel

theorem sys_elf (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (hl : ElfLoaded (byteAt sysElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform sysLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords sysLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords sysLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ T ls w, q.trace = ls.map A64.Event.sys ∧
        Images arm64Flags sysShimLayout ⟨args, environ, false⟩ [] T ls ∧ Carried R 0 ls ∧
        (∀ e ∈ ls, WritesNative sysShimLayout (wasiCap * 65536) e) ∧
        Linux.writeData 1 ls = committedWrites 1 T ∧
        ((∃ c, Exec (linuxHost arm64Flags sysShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.exited c) w ∧ q.core.x 0 = c) ∨
          (Exec (linuxHost arm64Flags sysShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped exitRejected) w ∧ q.core.x 0 = 1) ∨
          (Exec (linuxHost arm64Flags sysShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped shimTrap) w ∧ q.core.x 0 = 2) ∨
          ((∃ residual, Prefix (linuxHost arm64Flags sysShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            residual w) ∧ q.core.x 0 = 2)) := by
  obtain ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, himg, hcar, hwq, hend⟩ :=
    wasiElf_footprint sys_elf_file (sys_elf_segments.trans sys_elf_layout.symm)
      (by rw [command.module, compile_imports_with]) calls_supported (by decide)
      sys_elf_room (fun I R => linux_footprint_native arm64Flags _ I R (by decide)) R p hl
      hstack hpc htr
  refine ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, himg, hcar, hwq, himg.writeData 1, ?_⟩
  rcases hend with h | h | h | ⟨-, h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

#print axioms sys_elf_file
#print axioms sys_elf_segments
#print axioms sys_elf_layout
#print axioms sys_elf_entry
#print axioms sys_elf_room
#print axioms sys_elf

end TestSupport.A64.ImageFilesWasiSys
