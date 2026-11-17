import TestSupport.A64.WasiElf
import Verified.Examples.WasiClockRandomNative
import LeanExe.A64.File

/-!
The theorems of the Linux executable that `a64-wasi emit` writes for the clock and random command,
a WASI command that reads three clocks and two buffers of random bytes and writes what they gave.
`tests/linux/a64-wasi.sh` elaborates this file in the directory of the executable, so `file_nat%`
and `file_size%` read clockrandom.elf, and no build target includes it.  The kernel evaluates
`genWasiElf` on the command's module, the index of `_start`, the stack's room, and the cap, and
checks that the executable's bytes are the file's (`clockrandom_elf_file`).
`clockrandom_elf_segments` states the two program headers that `elfSegments` reads from the file,
the premise of `ElfLoaded`, and `clockrandom_elf_layout` that they are those of the generator's
layout.  `clockrandom_elf_entry` states that the file's entry is the prefix `wasiEntry`, and
`clockrandom_elf_room` that the stack's room holds the module's stack bound.

`clockrandom_elf` holds for every reply sequence.  From a process whose memory holds the file as
Linux's loader places it, with the arguments `args` and the environment `environ` on Linux's initial
stack at SP, the program counter at the entry, and no event in the trace, the process reaches `SVC
#0` with X8 at 94, `exit_group`, with the UART's state as it was.  Its trace holds the layer events
`ls`, the images of the WASI events `T` of a run of the command's action under `linuxHost` at
arm64's open flags and the launch `⟨args, environ, false⟩`, each of which holds its reply and writes
within the cap's linear memory or is a `clock_gettime` into the timespec, and the writes of
descriptor 1 in `ls` took the bytes that the `fd_write` events of `T` to standard output committed.
`T` is the trace of an `Exec` run that ends at an accepted exit, whose status X0 holds, at an exit
that the shim rejects, with X0 at 1, or at a trap of the shim, with X0 at 2, or of a `Prefix` run of
the action, with X0 at 2.  The command imports `clock_time_get` and `random_get`, whose stubs
`flatStub_sim` covers, and `wasiElf_footprint` gives these facts.
-/

namespace TestSupport.A64.ImageFilesWasiClockElf

open LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim Verified.ShimA64
  Verified.Examples.WasiClockRandom TestSupport.A64.WasiElf

def clockRandomElfBytes : Nat := file_nat% "clockrandom.elf"
def clockRandomElfSize : Nat := file_size% "clockrandom.elf"

/-- The executable's layout. -/
def clockRandomLayout : ElfLayout := wasiLayout command.module clockRandomStart wasiRoom wasiCap

/-- The shim's layout of the executable. -/
def clockRandomShimLayout : ShimLayout :=
  wasiShimLayout command.module clockRandomStart wasiRoom wasiCap

set_option maxRecDepth 100000

theorem clockrandom_elf_file :
    bytesOk (genWasiElf command.module clockRandomStart wasiRoom wasiCap)
    clockRandomElfBytes clockRandomElfSize = true := by decide +kernel

theorem clockrandom_elf_segments : elfSegments (byteAt clockRandomElfBytes) =
    [⟨1, 5, 0, 0x400000, 14156, 14156⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem clockrandom_elf_layout : elfSegmentsOf clockRandomLayout =
    [⟨1, 5, 0, 0x400000, 14156, 14156⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem clockrandom_elf_entry : elfEntryOf (byteAt clockRandomElfBytes) = wasiEntry.toNat := by
  decide +kernel

theorem clockrandom_elf_room :
    wasiStackBound command.module clockRandomStart ≤ wasiRoom.toNat := by
  decide +kernel

theorem clockrandom_elf (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (hl : ElfLoaded (byteAt clockRandomElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform clockRandomLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords clockRandomLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords clockRandomLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ T ls w, q.trace = ls.map A64.Event.sys ∧
        Images arm64Flags clockRandomShimLayout ⟨args, environ, false⟩ [] T ls ∧
        Carried R 0 ls ∧ (∀ e ∈ ls, WritesNative clockRandomShimLayout (wasiCap * 65536) e) ∧
        Linux.writeData 1 ls = committedWrites 1 T ∧
        ((∃ c, Exec (linuxHost arm64Flags clockRandomShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.exited c) w ∧ q.core.x 0 = c) ∨
          (Exec (linuxHost arm64Flags clockRandomShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped exitRejected) w ∧ q.core.x 0 = 1) ∨
          (Exec (linuxHost arm64Flags clockRandomShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped shimTrap) w ∧ q.core.x 0 = 2) ∨
          ((∃ residual, Prefix (linuxHost arm64Flags clockRandomShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            residual w) ∧ q.core.x 0 = 2)) := by
  obtain ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, himg, hcar, hwq, hend⟩ :=
    wasiElf_footprint (calls := command.sysCalls) clockrandom_elf_file
      (clockrandom_elf_segments.trans clockrandom_elf_layout.symm)
      (by rw [command.module, compile_imports_with]) calls_supported (by decide)
      clockrandom_elf_room
      (fun I R => linux_footprint_native arm64Flags _ I R (by decide)) R p hl hstack hpc htr
  refine ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, himg, hcar, hwq, himg.writeData 1, ?_⟩
  rcases hend with h | h | h | ⟨-, h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

#print axioms clockrandom_elf_file
#print axioms clockrandom_elf_segments
#print axioms clockrandom_elf_layout
#print axioms clockrandom_elf_entry
#print axioms clockrandom_elf_room
#print axioms clockrandom_elf

end TestSupport.A64.ImageFilesWasiClockElf
