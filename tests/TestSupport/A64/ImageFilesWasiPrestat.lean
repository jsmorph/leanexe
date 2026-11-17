import TestSupport.A64.WasiElf
import Verified.Examples.WasiPrestatNative
import LeanExe.A64.File

/-!
The theorems of the Linux executable that `a64-wasi emit` writes for the prestat command, a WASI
command that writes what `fd_prestat_get` and `fd_prestat_dir_name` answer for descriptor 3.
`tests/linux/a64-wasi-preopen.sh` elaborates this file in the directory of the executable, so
`file_nat%` and `file_size%` read prestat.elf, and no build target includes it.  The kernel
evaluates `genWasiElf` on the command's module, the index of `_start`, the stack's room, and the
cap, and checks that the executable's bytes are the file's (`prestat_elf_file`).
`prestat_elf_segments` states the two program headers that `elfSegments` reads from the file, the
premise of `ElfLoaded`, and `prestat_elf_layout` that they are those of the generator's layout.
`prestat_elf_entry` states that the file's entry is the prefix `wasiEntry`, and
`prestat_elf_room` that the stack's room holds the module's stack bound.

The command imports the prestat functions, so the executable starts with the check of descriptor
3, whose events and outcome `preopenRun` gives for the path buffer of the scratch and the replies
from the first on.  `prestat_elf` states, for every reply sequence, from a process whose memory
holds the file as Linux's loader places it, whose initial stack holds the arguments and the
environment, with the program counter at the entry and no event in the trace, that the process
reaches `SVC #0` with X8 at 94, `exit_group`, with the UART's state as it was.  When the check
ends the run, the trace holds its events and X0 holds 67.  Otherwise the launch grants descriptor
3 as the check found it, and the trace holds the check's events and then the layer events `ls`, the
images of the WASI events `T` of a run of the command's action under `linuxHost` with the replies
after the check's.  Each event of `ls` holds its reply and writes within the cap's linear memory or
is a `clock_gettime` into the timespec.  The run is an accepted exit, whose status X0 holds, an
exit that the shim rejects, with X0 at 1, a trap of the shim, with X0 at 2, or a trap of the guest
after a prefix of the action, with X0 at 2.
-/

namespace TestSupport.A64.ImageFilesWasiPrestat

open LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim Verified.ShimA64
  Verified.Examples.WasiPrestat TestSupport.A64.WasiElf

def prestatElfBytes : Nat := file_nat% "prestat.elf"
def prestatElfSize : Nat := file_size% "prestat.elf"

/-- The executable's layout. -/
def prestatLayout : ElfLayout := wasiLayout command.module prestatStart wasiRoom wasiCap

/-- The shim's layout of the executable. -/
def prestatShimLayout : ShimLayout := wasiShimLayout command.module prestatStart wasiRoom wasiCap

/-- The shim's scratch of the executable. -/
def prestatScratch : Scratch := wasiScratch command.module prestatStart wasiRoom wasiCap

set_option maxRecDepth 100000

theorem prestat_elf_file : bytesOk (genWasiElf command.module prestatStart wasiRoom wasiCap)
    prestatElfBytes prestatElfSize = true := by decide +kernel

theorem prestat_elf_segments : elfSegments (byteAt prestatElfBytes) = SEGMENTS := by
  decide +kernel

theorem prestat_elf_layout : elfSegmentsOf prestatLayout = SEGMENTS := by
  decide +kernel

theorem prestat_elf_entry : elfEntryOf (byteAt prestatElfBytes) = wasiEntry.toNat := by
  decide +kernel

theorem prestat_elf_room : wasiStackBound command.module prestatStart ≤ wasiRoom.toNat := by
  decide +kernel

theorem prestat_elf (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (hl : ElfLoaded (byteAt prestatElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform prestatLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords prestatLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords prestatLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      match preopenRun prestatScratch.path R 0 with
      | (l₀, none) => q.trace = l₀.map A64.Event.sys ∧ q.core.x 0 = 67
      | (l₀, some granted) =>
        ∃ T ls w, q.trace = (l₀ ++ ls).map A64.Event.sys ∧
          Images arm64Flags prestatShimLayout ⟨args, environ, granted⟩ [] T ls ∧
          Carried R l₀.length ls ∧
          (∀ e ∈ ls, WritesNative prestatShimLayout (wasiCap * 65536) e) ∧
          ((∃ c, Exec (linuxHost arm64Flags prestatShimLayout ⟨args, environ, granted⟩
                (fun j => R (l₀.length + j)))
              (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
              (.exited c) w ∧ q.core.x 0 = c) ∨
            (Exec (linuxHost arm64Flags prestatShimLayout ⟨args, environ, granted⟩
                (fun j => R (l₀.length + j)))
              (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
              (.trapped exitRejected) w ∧ q.core.x 0 = 1) ∨
            (Exec (linuxHost arm64Flags prestatShimLayout ⟨args, environ, granted⟩
                (fun j => R (l₀.length + j)))
              (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
              (.trapped shimTrap) w ∧ q.core.x 0 = 2) ∨
            ((∃ residual, Prefix (linuxHost arm64Flags prestatShimLayout ⟨args, environ, granted⟩
                (fun j => R (l₀.length + j)))
              (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
              residual w) ∧ q.core.x 0 = 2)) := by
  have himp : command.module.imports = ABI.importsWith command.sysCalls := by
    rw [command.module, compile_imports_with]
  obtain ⟨q, rq, cq, x8q, ioq, hq⟩ :=
    wasiElf_footprint (calls := command.sysCalls) prestat_elf_file
      (prestat_elf_segments.trans prestat_elf_layout.symm) himp calls_supported (by decide)
      prestat_elf_room
      (fun I R => linux_footprint_native arm64Flags _ I R (by decide)) R p hl hstack hpc htr
  have hsu : startup (needsCheck (command.module.imports.drop 3))
      (wasiScratch command.module prestatStart wasiRoom wasiCap) R =
      preopenRun prestatScratch.path R 0 := by
    rw [himp]
    rfl
  refine ⟨q, rq, cq, x8q, ioq, ?_⟩
  rw [hsu] at hq
  generalize preopenRun prestatScratch.path R 0 = pr at hq ⊢
  rcases pr with ⟨l₀, _ | granted⟩
  · exact hq
  · obtain ⟨T, ls, w, trq, himg, hcar, hwq, hend⟩ := hq
    refine ⟨T, ls, w, trq, himg, hcar, hwq, ?_⟩
    rcases hend with h | h | h | ⟨-, h⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))

#print axioms prestat_elf_file
#print axioms prestat_elf_segments
#print axioms prestat_elf_layout
#print axioms prestat_elf_entry
#print axioms prestat_elf_room
#print axioms prestat_elf

end TestSupport.A64.ImageFilesWasiPrestat
