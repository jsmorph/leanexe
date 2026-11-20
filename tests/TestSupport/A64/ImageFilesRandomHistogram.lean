import TestSupport.A64.WasiElf
import TestSupport.A64.ElfWitness
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

`histogram_elf_counts` is the corollary for the file, for every reply sequence and every N, from
arguments whose strings, each with its zero byte, and eight-byte pointers take at most `argsLimit`
bytes, as Linux requires of every process.  `budget`, the bound of `body_bounded` at arguments of
`argsLimit` bytes, fits the executable's 4,096 pages.  When every `getrandom` of the trace
returned an error number or a count of at most its length, positive for a positive length, and
every `write` an error number or at most its count (`InRange`), X0 and the trace meet `Counts`.
`histogram_elf_runs` gives the run from `linux_footprint_bounded`, the footprint without a guest
trap, through `wasiElf_footprint_with`, and `linux_exec_counts` gives the status and `Counts` from
the `Exec` run that the footprint names, with `Sized` from the replies that the events hold
(`carried_sized`).

`histogram_elf_witness` shows that the corollary's premises and `InRange` hold together with a
short read.  The process holds the file in memory as `ElfLoaded` states and, at SP `2^32`, the
initial stack of the arguments `oneArgs`, `h` and `1`, with no environment, as `loadedMem` of
`tests/TestSupport/A64/ElfWitness.lean` places them.  Under the replies `shortReplies`, which
answer calls 0 and 1 with the result 4 and zero bytes and every later call with the size of
`oneOutput`, the process reaches `exit_group` with X0 at 0 after layer events that meet `InRange`
and `Counts` and hold a `getrandom` that returned a count of at least 1 and below its length
(`ShortRead`).
-/

namespace TestSupport.A64.ImageFilesRandomHistogram

open LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim Verified.ShimA64
  Demos.RandomHistogram TestSupport.A64.WasiElf TestSupport.A64.ElfWitness

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
    [⟨1, 5, 0, 0x400000, 22008, 22008⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem histogram_elf_layout : elfSegmentsOf histogramLayout =
    [⟨1, 5, 0, 0x400000, 22008, 22008⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
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


/-- The runs of the file from arguments within the limits of the corollary: the process reaches
`exit_group` after the layer events `ls`, which hold their replies, and `ls` are the images of the
WASI events `T` of an `Exec` run of the command's action that ends at an accepted exit, whose
status X0 holds, at an exit that the shim rejects, or at a trap of the shim. -/
theorem histogram_elf_runs (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (small : stringsSize args + 8 * args.length ≤ argsLimit)
    (hl : ElfLoaded (byteAt histogramElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform histogramLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords histogramLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords histogramLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ T ls w, q.trace = ls.map A64.Event.sys ∧
        Images arm64Flags histogramShimLayout ⟨args, environ, false⟩ [] T ls ∧ Carried R 0 ls ∧
        ((∃ c, Exec (linuxHost arm64Flags histogramShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.exited c) w ∧ q.core.x 0 = c) ∨
          Exec (linuxHost arm64Flags histogramShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped exitRejected) w ∨
          Exec (linuxHost arm64Flags histogramShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped shimTrap) w) := by
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
        exact linux_footprint_bounded arm64Flags _ ⟨args, environ, false⟩ R small (by decide)
          budget_fits)
      hl hstack hpc htr
  rw [hsu] at hq
  obtain ⟨T, ls, w, trq, himg, hcar, -, hend⟩ := hq
  rw [List.nil_append] at trq
  rw [hR] at hend
  refine ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, himg, hcar, ?_⟩
  rcases hend with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨impossible, -⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)
  · cases impossible

/-- The random histogram's corollary for `histogram.elf`.  For every reply sequence `R`, a process
started as for `histogram_elf` with arguments whose strings, each with its zero byte, and
eight-byte pointers take at most `argsLimit` bytes, 6 MiB, reaches `SVC #0` with X8 at 94,
`exit_group`, and the UART's state as it was.  Its
trace holds the layer events `ls`, each of which holds its reply of `R`, and when every
`getrandom` of `ls` returned an error number or a count of at most its length, positive for a
positive length, and every `write` an error number or at most its count (`InRange`), X0 and `ls`
meet `Counts`.  When `parseSpec` refuses the arguments, no layer event
precedes `exit_group`, and X0 is 2.  Otherwise the events start with groups of `getrandom` calls
that mirror, one for one, the calls of `random_get` of `Draws` for N words, each for `8 · min r 512`
bytes with `r` the words still to draw.  A group's calls ask with flags 0 for the bytes that the
calls before them did not return, and a group whose `random_get` returned errno 0 returned that
call's bytes.  Either the last group ended with an error number, whose errno is X0, and no `write`
follows, or calls of `write` of descriptor 1 follow, the random bytes hold exactly N little-endian
words `w`, the counts of `histogramSpec w` sum to N, the writes number at most one more than the
bytes of `renderSpec (histogramSpec w)`, each offered at least one byte, the bytes of that output
that the writes before it did not take, and the bytes that the writes took form a prefix of that
output.  In the second case X0 is 0 exactly when they are the
whole output, and otherwise X0 is 77 after one write for each of the loop's passes, each of which
returned at most its count, or the errno of the error number that the last `write` returned,
every `write` before which returned at most its count. -/
theorem histogram_elf_counts (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (small : stringsSize args + 8 * args.length ≤ argsLimit)
    (hl : ElfLoaded (byteAt histogramElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform histogramLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords histogramLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords histogramLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ ls, q.trace = ls.map A64.Event.sys ∧ Carried R 0 ls ∧
        (InRange ls → Counts args ls (q.core.x 0)) := by
  obtain ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, himg, hcar, hend⟩ :=
    histogram_elf_runs R p small hl hstack hpc htr
  refine ⟨q, rq, cq, x8q, ioq, ls, trq, hcar, fun range => ?_⟩
  have sized := carried_sized hcar
  rcases hend with ⟨c, h, hx⟩ | h | h
  · obtain ⟨c', exited, counts⟩ := linux_exec_counts small h himg range sized
    cases exited
    rw [hx]
    exact counts
  · obtain ⟨_, exited, -⟩ := linux_exec_counts small h himg range sized
    cases exited
  · obtain ⟨_, exited, -⟩ := linux_exec_counts small h himg range sized
    cases exited

/-! ## The premises hold together -/

/-- The premises of `histogram_elf_counts` and `InRange` hold together with a short read.  For the
replies `shortReplies`, the process `witnessProc`, the arguments `oneArgs`, which give N of 1, no
environment, and the stack's top `witnessTop`, every premise of the corollary holds, and the
process reaches `exit_group` with X0 at 0 after layer events that hold their replies, meet
`InRange` and `Counts`, and hold a short read, a `getrandom` that returned a count of at least 1
and below its length (`ShortRead`). -/
theorem histogram_elf_witness :
    ∃ (R : Linux.Replies) (p : Proc) (args environ : List (List UInt8)) (top : UInt64),
      parseSpec (bytesOfList (stringsBytes args)) = 1 ∧
      stringsSize args + 8 * args.length ≤ argsLimit ∧
      ElfLoaded (byteAt histogramElfBytes) p.core.mem ∧
      InitialStack args environ p.core.sp top p.core.mem ∧ p.core.pc = wasiEntry ∧
      p.trace = [] ∧
      ∃ q, ProcReachWith Linux.table R (wasiPlatform histogramLayout p.core.sp top)
          (fetchFrom p.core.mem elfEntry (elfWords histogramLayout)) p q ∧
        fetchFrom p.core.mem elfEntry (elfWords histogramLayout) q.core.pc = some svcWord ∧
        q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
        ∃ ls, q.trace = ls.map A64.Event.sys ∧ Carried R 0 ls ∧ InRange ls ∧ ShortRead ls ∧
          Counts args ls (q.core.x 0) ∧ q.core.x 0 = 0 := by
  have parsed : parseSpec (bytesOfList (stringsBytes oneArgs)) = 1 := by decide
  have small : stringsSize oneArgs + 8 * oneArgs.length ≤ argsLimit := by decide
  have loaded : ElfLoaded (byteAt histogramElfBytes)
      (loadedMem (byteAt histogramElfBytes) 22008 4096 witnessStack) :=
    loadedMem_loaded histogram_elf_segments (by decide) (by decide)
  have stack : InitialStack oneArgs [] (2 ^ 32) witnessTop
      (loadedMem (byteAt histogramElfBytes) 22008 4096 witnessStack) :=
    loadedMem_stack (byteAt histogramElfBytes) 22008 4096
  refine ⟨shortReplies, witnessProc (loadedMem (byteAt histogramElfBytes) 22008 4096 witnessStack),
    oneArgs, [], witnessTop, parsed, small, loaded, stack, rfl, rfl, ?_⟩
  obtain ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, himg, hcar, hend⟩ :=
    histogram_elf_runs shortReplies
      (witnessProc (loadedMem (byteAt histogramElfBytes) 22008 4096 witnessStack)) small loaded
      stack rfl rfl
  refine ⟨q, rq, cq, x8q, ioq, ls, trq, hcar, ?_⟩
  rcases hend with ⟨c, h, hx⟩ | h | h
  · obtain ⟨exited, range, short⟩ := short_run h himg hcar
    cases exited
    obtain ⟨c', exited, counts⟩ := linux_exec_counts small h himg range (carried_sized hcar)
    cases exited
    exact ⟨range, short, by rw [hx]; exact counts, hx⟩
  · cases (short_run h himg hcar).1
  · cases (short_run h himg hcar).1

#print axioms histogram_elf_file
#print axioms histogram_elf_segments
#print axioms histogram_elf_layout
#print axioms histogram_elf_entry
#print axioms histogram_elf_room
#print axioms histogram_elf
#print axioms histogram_elf_runs
#print axioms histogram_elf_counts
#print axioms histogram_elf_witness

end TestSupport.A64.ImageFilesRandomHistogram
