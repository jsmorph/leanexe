import TestSupport.A64.WasiElf
import Verified.Examples.WasiReadAllNative
import LeanExe.A64.File

/-!
The theorems of the Linux executable that `a64-wasi emit` writes for the readAll command, a WASI
command that copies standard input to standard output.  `tests/linux/a64-wasi.sh` elaborates this
file in the directory of the executable, so `file_nat%` and `file_size%` read readall.elf, and no
build target includes it.  The kernel evaluates `genWasiElf` on the command's module, the index of
`_start`, the stack's room, and the cap, and checks that the executable's bytes are the file's
(`readall_elf_file`).  `readall_elf_segments` states the two program headers that `elfSegments`
reads from the file, the premise of `ElfLoaded`, and `readall_elf_layout` that they are those of
the generator's layout.  `readall_elf_entry` states that the file's entry is `elfEntry`, and
`readall_elf_room` that the stack's room holds the module's stack bound.

`readall_elf` holds for every reply sequence.  From a process whose memory holds the file as
Linux's loader places it, with the program counter at the entry and no event in the trace, the
process reaches `SVC #0` with X8 at 94, `exit_group`, with the UART's state as it was.  Its trace
holds the layer events `ls`, the images of the WASI events `T` of a run of the command's action
under `linuxHost`, each of which holds its reply and has its output region within the cap's linear
memory.  The
reads of descriptor 0 in `ls` returned the bytes that the `fd_read` events of `T` committed, and
its writes of descriptor 1 took the bytes that the `fd_write` events of `T` to standard output
committed.  The run is an accepted exit, whose status X0 holds, an exit that the shim rejects,
with X0 at 1, a trap of the shim, with X0 at 2, or a trap of the guest after a prefix of the
action, with X0 at 2.
-/

namespace TestSupport.A64.ImageFilesWasiElf

open LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim Verified.ShimA64
  Verified.Examples.WasiReadAll TestSupport.A64.WasiElf

def readAllElfBytes : Nat := file_nat% "readall.elf"
def readAllElfSize : Nat := file_size% "readall.elf"

/-- The executable's layout. -/
def readAllLayout : ElfLayout := wasiLayout command.module readAllStart wasiRoom wasiCap

set_option maxRecDepth 100000

theorem readall_elf_file : bytesOk (genWasiElf command.module readAllStart wasiRoom wasiCap)
    readAllElfBytes readAllElfSize = true := by decide +kernel

theorem readall_elf_segments : elfSegments (byteAt readAllElfBytes) =
    [⟨1, 5, 0, 0x400000, 11580, 11580⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268505104⟩] := by
  decide +kernel

theorem readall_elf_layout : elfSegmentsOf readAllLayout =
    [⟨1, 5, 0, 0x400000, 11580, 11580⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268505104⟩] := by
  decide +kernel

theorem readall_elf_entry : elfEntryOf (byteAt readAllElfBytes) = elfEntry.toNat := by
  decide +kernel

theorem readall_elf_room : wasiStackBound command.module readAllStart ≤ wasiRoom.toNat := by
  decide +kernel

theorem readall_elf (R : Linux.Replies) (p : Proc)
    (hl : ElfLoaded (byteAt readAllElfBytes) p.core.mem) (hpc : p.core.pc = elfEntry)
    (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (elfPlatform readAllLayout)
        (fetchFrom p.core.mem elfEntry (elfWords readAllLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords readAllLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ T ls w, q.trace = ls.map A64.Event.sys ∧ Images T ls ∧ Carried R 0 ls ∧
        (∀ e ∈ ls, WritesWithin (layoutAt readAllLayout.area) (wasiCap * 65536) e) ∧
        Linux.readData 0 ls = committedReads T ∧
        Linux.writeData 1 ls = committedWrites .stdout T ∧
        ((∃ c, Exec (linuxHost (layoutAt readAllLayout.area) R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.exited c) w ∧ q.core.x 0 = c) ∨
          (Exec (linuxHost (layoutAt readAllLayout.area) R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped exitRejected) w ∧ q.core.x 0 = 1) ∨
          (Exec (linuxHost (layoutAt readAllLayout.area) R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped shimTrap) w ∧ q.core.x 0 = 2) ∨
          ((∃ residual, Prefix (linuxHost (layoutAt readAllLayout.area) R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            residual w) ∧ q.core.x 0 = 2)) := by
  obtain ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, himg, hcar, hwq, hend⟩ :=
    wasiElf_footprint readall_elf_file (readall_elf_segments.trans readall_elf_layout.symm)
      (by decide) readall_elf_room
      (fun R => linux_footprint_native (layoutAt readAllLayout.area) R (by decide)) R p hl hpc
      htr
  refine ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, himg, hcar, hwq, himg.readData,
    himg.writeData .stdout, ?_⟩
  rcases hend with h | h | h | ⟨-, h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

#print axioms readall_elf_file
#print axioms readall_elf_segments
#print axioms readall_elf_layout
#print axioms readall_elf_entry
#print axioms readall_elf_room
#print axioms readall_elf

end TestSupport.A64.ImageFilesWasiElf
