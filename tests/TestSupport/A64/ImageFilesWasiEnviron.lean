import TestSupport.A64.WasiElf
import Verified.Examples.WasiSysEnvironNative
import LeanExe.A64.File

/-!
The theorems of the Linux executable that `a64-wasi emit` writes for the environment command of
`Verified.Examples.WasiSysEnviron`, a WASI command that writes the count and the size of its
environment and then its variables.  `tests/linux/a64-wasi.sh` elaborates this file in the
directory of the executable, so `file_nat%` and `file_size%` read environ.elf, and no build target
includes it.  The kernel evaluates `genWasiElf` on the command's module, the index of `_start`, the
stack's room, and the cap, and checks that the executable's bytes are the file's
(`environ_elf_file`).  `environ_elf_segments` states the two program headers that `elfSegments`
reads from the file, `environ_elf_layout` that they are those of the generator's layout,
`environ_elf_entry` that the file's entry is the prefix `wasiEntry`, and `environ_elf_room` that
the stack's room holds the module's stack bound.

`environ_elf` holds for every reply sequence.  From a process whose memory holds the file as
Linux's loader places it, with the arguments `args` and the environment `environ` on Linux's
initial stack at SP, the program counter at the entry, and no event in the trace, the process
reaches `SVC #0` with X8 at 94, `exit_group`, with the UART's state as it was.  Its trace holds the
layer events `ls`, the images of the WASI events `T` of a run of the command's action under
`linuxHost` with the launch `⟨args, environ, false⟩`, so the variables that the run's
`environ_sizes_get` and `environ_get` report are those of `environ`, which the stubs read through
the initial SP that `main` saved.  Each event of `ls` holds its reply and writes within the cap's
linear memory or into the timespec, and the writes of descriptor 1 in `ls` took the bytes that the
`fd_write` events of `T` to standard output committed.  The run is an accepted exit, whose status
X0 holds, an exit that the shim rejects, with X0 at 1, a trap of the shim, with X0 at 2, or a trap
of the guest after a prefix of the action, with X0 at 2.
-/

namespace TestSupport.A64.ImageFilesWasiEnviron

open LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim Verified.ShimA64
  Verified.Examples.WasiSysEnviron TestSupport.A64.WasiElf

def environElfBytes : Nat := file_nat% "environ.elf"
def environElfSize : Nat := file_size% "environ.elf"

/-- The executable's layout. -/
def environLayout : ElfLayout := wasiLayout command.module environStart wasiRoom wasiCap

/-- The shim's layout of the executable. -/
def environShimLayout : ShimLayout :=
  wasiShimLayout command.module environStart wasiRoom wasiCap

set_option maxRecDepth 100000

theorem environ_elf_file : bytesOk (genWasiElf command.module environStart wasiRoom wasiCap)
    environElfBytes environElfSize = true := by decide +kernel

theorem environ_elf_segments : elfSegments (byteAt environElfBytes) =
    [⟨1, 5, 0, 0x400000, 11256, 11256⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem environ_elf_layout : elfSegmentsOf environLayout =
    [⟨1, 5, 0, 0x400000, 11256, 11256⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem environ_elf_entry : elfEntryOf (byteAt environElfBytes) = wasiEntry.toNat := by
  decide +kernel

theorem environ_elf_room : wasiStackBound command.module environStart ≤ wasiRoom.toNat := by
  decide +kernel

theorem environ_elf (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (hl : ElfLoaded (byteAt environElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform environLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords environLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords environLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ T ls w, q.trace = ls.map A64.Event.sys ∧
        Images arm64Flags environShimLayout ⟨args, environ, false⟩ [] T ls ∧ Carried R 0 ls ∧
        (∀ e ∈ ls, WritesNative environShimLayout (wasiCap * 65536) e) ∧
        Linux.writeData 1 ls = committedWrites 1 T ∧
        ((∃ c, Exec (linuxHost arm64Flags environShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.exited c) w ∧ q.core.x 0 = c) ∨
          (Exec (linuxHost arm64Flags environShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped exitRejected) w ∧ q.core.x 0 = 1) ∨
          (Exec (linuxHost arm64Flags environShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped shimTrap) w ∧ q.core.x 0 = 2) ∨
          ((∃ residual, Prefix (linuxHost arm64Flags environShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            residual w) ∧ q.core.x 0 = 2)) := by
  have himp : command.module.imports = ABI.importsWith command.sysCalls := by
    rw [command.module, compile_imports_with]
  obtain ⟨q, rq, cq, x8q, ioq, hq⟩ :=
    wasiElf_footprint environ_elf_file (environ_elf_segments.trans environ_elf_layout.symm)
      himp calls_supported (by decide)
      environ_elf_room (fun I R => linux_footprint_native arm64Flags _ I R (by decide)) R p hl
      hstack hpc htr
  have hsu : startup (needsCheck (command.module.imports.drop 3))
      (wasiScratch command.module environStart wasiRoom wasiCap) R = ([], some false) := by
    rw [himp]
    rfl
  rw [hsu] at hq
  obtain ⟨T, ls, w, trq, himg, hcar, hwq, hend⟩ := hq
  rw [List.nil_append] at trq
  have hR : (fun j => R (([] : List Linux.Event).length + j)) = R := funext fun j => by simp
  rw [hR] at hend
  refine ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, himg, hcar, hwq, himg.writeData 1, ?_⟩
  rcases hend with h | h | h | ⟨-, h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

#print axioms environ_elf_file
#print axioms environ_elf_segments
#print axioms environ_elf_layout
#print axioms environ_elf_entry
#print axioms environ_elf_room
#print axioms environ_elf

end TestSupport.A64.ImageFilesWasiEnviron
