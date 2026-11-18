import TestSupport.A64.WasiElf
import Demos.RandomHistogram.NativeCounts
import LeanExe.A64.File

/-!
The theorems of the Linux executable that `a64-wasi wasm` writes for the random-residue histogram's
command of `Demos/RandomHistogram/Command.lean`, which takes N on its command line, draws N random
words with `random_get`, and writes the counts of their residues mod 10.  `tests/linux/a64-wasi.sh`
elaborates this file in the directory of the executable, so `file_nat%` and `file_size%` read
histogram.elf, and no build target includes it.  The kernel evaluates `genWasiElf` on the
command's module, the index of `_start`, the stack's room, and the cap, and checks that the
executable's bytes are the file's (`histogram_elf_file`).  `histogram_elf_segments` states the two
program headers that `elfSegments` reads from the file, `histogram_elf_layout` that they are those
of the generator's layout, `histogram_elf_entry` that the file's entry is the prefix `wasiEntry`,
and `histogram_elf_room` that the stack's room holds the module's stack bound.

`histogram_elf` holds for every reply sequence.  From a process whose memory holds the file as
Linux's loader places it, with the arguments `args` and the environment `environ` on Linux's
initial stack at SP, the program counter at the entry, and no event in the trace, the process
reaches `SVC #0` with X8 at 94, `exit_group`, with the UART's state as it was.  Its trace holds the
layer events `ls`, the images of the WASI events `T` of a run of the command's action under
`linuxHost` with the launch `⟨args, environ, false⟩`, so the arguments that the run's
`args_sizes_get` and `args_get` report are those of `args`.  Each event of `ls` holds its reply
and writes within the cap's linear memory or into the timespec, and the writes of descriptor 1 in
`ls` took the bytes that the `fd_write` events of `T` to standard output committed.  `T` is the
trace of an `Exec` run that ends at an accepted exit, whose status X0 holds, at an exit that the
shim rejects, with X0 at 1, or at a trap of the shim, with X0 at 2, or of a `Prefix` run of the
action, with X0 at 2.

`histogram_elf_counts` is the corollary for the file, for every reply sequence, from arguments
whose strings, each with its zero byte, and eight-byte pointers take at most `argsLimit` bytes, as
Linux requires of every process, and whose N is at most `drawLimit`, the largest N for which the
resource model's charge of `main` fits the executable's 4,096 pages.  When every `getrandom` of
the trace returned the count that it asked for and every `write` the count that it offered, X0 and
the trace meet `Counts`.  `wasiElf_footprint_with` gives the run from `linux_footprint_bounded`,
the footprint without a guest trap, and `linux_exec_counts` gives the status and `Counts` from the
`Exec` run that the footprint names.
-/

namespace TestSupport.A64.ImageFilesRandomHistogram

open LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim Verified.ShimA64
  Demos.RandomHistogram TestSupport.A64.WasiElf

def histogramElfBytes : Nat := file_nat% "histogram.elf"
def histogramElfSize : Nat := file_size% "histogram.elf"

/-- The executable's layout. -/
def histogramLayout : ElfLayout := wasiLayout command.module startIndex wasiRoom wasiCap

/-- The shim's layout of the executable. -/
def histogramShimLayout : ShimLayout := wasiShimLayout command.module startIndex wasiRoom wasiCap

set_option maxRecDepth 100000

theorem histogram_elf_file : bytesOk (genWasiElf command.module startIndex wasiRoom wasiCap)
    histogramElfBytes histogramElfSize = true := by decide +kernel

theorem histogram_elf_segments : elfSegments (byteAt histogramElfBytes) =
    [⟨1, 5, 0, 0x400000, 26112, 26112⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem histogram_elf_layout : elfSegmentsOf histogramLayout =
    [⟨1, 5, 0, 0x400000, 26112, 26112⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem histogram_elf_entry : elfEntryOf (byteAt histogramElfBytes) = wasiEntry.toNat := by
  decide +kernel

theorem histogram_elf_room : wasiStackBound command.module startIndex ≤ wasiRoom.toNat := by
  decide +kernel

theorem histogram_elf (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (hl : ElfLoaded (byteAt histogramElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform histogramLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords histogramLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords histogramLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ T ls w, q.trace = ls.map A64.Event.sys ∧
        Images arm64Flags histogramShimLayout ⟨args, environ, false⟩ [] T ls ∧ Carried R 0 ls ∧
        (∀ e ∈ ls, WritesNative histogramShimLayout (wasiCap * 65536) e) ∧
        Linux.writeData 1 ls = committedWrites 1 T ∧
        ((∃ c, Exec (linuxHost arm64Flags histogramShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.exited c) w ∧ q.core.x 0 = c) ∨
          (Exec (linuxHost arm64Flags histogramShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped exitRejected) w ∧ q.core.x 0 = 1) ∨
          (Exec (linuxHost arm64Flags histogramShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped shimTrap) w ∧ q.core.x 0 = 2) ∨
          ((∃ residual, Prefix (linuxHost arm64Flags histogramShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            residual w) ∧ q.core.x 0 = 2)) := by
  have himp : command.module.imports = ABI.importsWith command.sysCalls := by
    rw [command.module, compile_imports_with]
  obtain ⟨q, rq, cq, x8q, ioq, hq⟩ :=
    wasiElf_footprint histogram_elf_file
      (histogram_elf_segments.trans histogram_elf_layout.symm) himp calls_supported (by decide)
      histogram_elf_room (fun I R => linux_footprint_native arm64Flags _ I R (by decide)) R p hl
      hstack hpc htr
  have hsu : startup (needsCheck (command.module.imports.drop 3))
      (wasiScratch command.module startIndex wasiRoom wasiCap) R = ([], some false) := by
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

/-- The random histogram's corollary for `histogram.elf`.  For every reply sequence `R`, a process
started as for `histogram_elf` with arguments whose strings, each with its zero byte, and
eight-byte pointers take at most `argsLimit` bytes, 6 MiB, and whose N is at most `drawLimit`,
12,839,935, reaches `SVC #0` with X8 at 94, `exit_group`, and the UART's state as it was.  Its
trace holds the layer events `ls`, each of which holds its reply of `R`, and when every
`getrandom` of `ls` returned the count that it asked for and every `write` the count that it
offered (`Full`), X0 and `ls` meet `Counts`: for N of 0, no call and status 2, and otherwise
exactly N little-endian words `w` in the bytes that `getrandom` returned, counts of
`histogramSpec w` that sum to N, the bytes of `renderSpec (histogramSpec w)` written to descriptor
1, and status 0. -/
theorem histogram_elf_counts (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (small : stringsSize args + 8 * args.length ≤ argsLimit)
    (drawn : (parseSpec (bytesOfList (stringsBytes args))).toNat ≤ drawLimit)
    (hl : ElfLoaded (byteAt histogramElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform histogramLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords histogramLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords histogramLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ ls, q.trace = ls.map A64.Event.sys ∧ Carried R 0 ls ∧
        (Full ls → Counts args ls (q.core.x 0)) := by
  have himp : command.module.imports = ABI.importsWith command.sysCalls := by
    rw [command.module, compile_imports_with]
  have hsu : startup (needsCheck (command.module.imports.drop 3))
      (wasiScratch command.module startIndex wasiRoom wasiCap) R = ([], some false) := by
    rw [himp]
    rfl
  have hR : (fun j => R (([] : List Linux.Event).length + j)) = R := funext fun j => by simp
  obtain ⟨q, rq, cq, x8q, ioq, hq⟩ :=
    wasiElf_footprint_with histogram_elf_file
      (histogram_elf_segments.trans histogram_elf_layout.symm) himp calls_supported (by decide)
      histogram_elf_room R p
      (fun l₀ granted h => by
        rw [hsu] at h
        cases h
        rw [hR]
        exact linux_footprint_bounded arm64Flags _ ⟨args, environ, false⟩ R small drawn
          (by decide) budget_fits)
      hl hstack hpc htr
  rw [hsu] at hq
  obtain ⟨T, ls, w, trq, himg, hcar, -, hend⟩ := hq
  rw [List.nil_append] at trq
  rw [hR] at hend
  refine ⟨q, rq, cq, x8q, ioq, ls, trq, hcar, fun full => ?_⟩
  rcases hend with ⟨c, h, hx⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨impossible, -⟩
  · obtain ⟨c', exited, counts⟩ := linux_exec_counts small h himg full
    cases exited
    rw [hx]
    exact counts
  · obtain ⟨_, exited, -⟩ := linux_exec_counts small h himg full
    cases exited
  · obtain ⟨_, exited, -⟩ := linux_exec_counts small h himg full
    cases exited
  · cases impossible

#print axioms histogram_elf_file
#print axioms histogram_elf_segments
#print axioms histogram_elf_layout
#print axioms histogram_elf_entry
#print axioms histogram_elf_room
#print axioms histogram_elf
#print axioms histogram_elf_counts

end TestSupport.A64.ImageFilesRandomHistogram
