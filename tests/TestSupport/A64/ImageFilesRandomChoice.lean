module

public import TestSupport.A64.WasiElf
public import TestSupport.A64.ElfWitness
public import Demos.RandomChoice.NativeChoices
public import LeanExe.A64.File

@[expose] public section

/-!
The theorems of the Linux executable that `a64-wasi wasm` writes for the unbiased random choice's
command of `Demos/RandomChoice/Command.lean`, which takes N and K on its command line and writes K
values chosen from [1, N] by rejection sampling of random words.  `tests/linux/a64-wasi.sh`
elaborates this file in the directory of the executable, so `file_nat%` and `file_size%` read
choice.elf, and no build target includes it.  The kernel evaluates `genWasiElf` on the command's
module, the index of `_start`, the stack's room, and the cap, and checks that the executable's
bytes are the file's (`choice_elf_file`).  `choice_elf_segments` states the two program headers
that `elfSegments` reads from the file, `choice_elf_layout` that they are those of the generator's
layout, `choice_elf_entry` that the file's entry is the prefix `wasiEntry`, and `choice_elf_room`
that the stack's room holds the module's stack bound.

`choice_elf` holds for every reply sequence.  From a process whose memory holds the file as Linux's
loader places it, with the arguments `args` and the environment `environ` on Linux's initial stack
at SP, the program counter at the entry, and no event in the trace, the process reaches `SVC #0`
with X8 at 94, `exit_group`, with the UART's state as it was.  Its trace holds the layer events
`ls`, the images of the WASI events `T` of a run of the command's action under `linuxHost` with the
launch `⟨args, environ, false⟩`, so the arguments that the run's `args_sizes_get` and `args_get`
report are those of `args`.  Each event of `ls` holds its reply and writes within the cap's linear
memory or is a `clock_gettime` into the timespec or a `statx` into the `statx` record, and the
writes of descriptor 1 in `ls` took the bytes that the `fd_write` events of `T` to standard output
committed.  `T` is the trace of an `Exec` run that ends at an accepted exit, whose status X0 holds,
at an exit that the shim rejects, with X0 at 1, or at a trap of the shim, with X0 at 2, or of a
`Prefix` run of the action, with X0 at 2.

`choice_elf_choices` is the corollary for the file, for every reply sequence and every N and K, from
arguments whose strings, each with its zero byte, and eight-byte pointers take at most the random
histogram's `argsLimit` bytes, as Linux requires of every process.  `budget`, the bound of
`body_bounded`, fits the executable's 4,096 pages (`budget_fits`).  When every `getrandom` of the
trace returned an error number or a count of at most its length, positive for a positive length, and
every `write` an error number or at most its count, its third argument (`InRange`), X0 and the trace
meet `Choices`.  `choice_elf_runs` gives the run from `linux_footprint_bounded`, the footprint
without a guest trap, through `wasiElf_footprint_with`, and `linux_exec_choices` gives the status
and `Choices` from the `Exec` run that the footprint names, with `Sized` from the replies that the
events hold (`carried_sized`).

`choice_elf_witness` shows that the corollary's premises and `InRange` hold together.  The process
holds the file in memory as `ElfLoaded` states and, at SP `2^32`, the initial stack of the arguments
`witnessArgs`, `c`, `1`, and `1`, with no environment, as `loadedMem` of
`tests/TestSupport/A64/ElfWitness.lean` places them.  Under the replies `witnessReplies`, which
answer the `getrandom` of the run's one pass with 4,096 zero bytes and its `write` of the line `1`
with 2, the process reaches `exit_group` with X0 at 0 after layer events that meet `InRange` and
`Choices`.
-/

namespace TestSupport.A64.ImageFilesRandomChoice

open LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim Verified.ShimA64
  Demos.RandomChoice TestSupport.A64.WasiElf

def choiceElfBytes : Nat := file_nat% "choice.elf"
def choiceElfSize : Nat := file_size% "choice.elf"

/-- The executable's layout. -/
def choiceLayout : ElfLayout := wasiLayout command.module startIndex wasiRoom wasiCap

/-- The shim's layout of the executable. -/
def choiceShimLayout : ShimLayout := wasiShimLayout command.module startIndex wasiRoom wasiCap

set_option maxRecDepth 100000

theorem choice_elf_file : bytesOk (genWasiElf command.module startIndex wasiRoom wasiCap)
    choiceElfBytes choiceElfSize = true := by decide +kernel

theorem choice_elf_segments : elfSegments (byteAt choiceElfBytes) =
    [⟨1, 5, 0, 0x400000, 19916, 19916⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem choice_elf_layout : elfSegmentsOf choiceLayout =
    [⟨1, 5, 0, 0x400000, 19916, 19916⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem choice_elf_entry : elfEntryOf (byteAt choiceElfBytes) = wasiEntry.toNat := by
  decide +kernel

theorem choice_elf_room : wasiStackBound command.module startIndex ≤ wasiRoom.toNat := by
  decide +kernel

theorem choice_elf (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (hl : ElfLoaded (byteAt choiceElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform choiceLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords choiceLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords choiceLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ T ls w, q.trace = ls.map A64.Event.sys ∧
        Images arm64Flags choiceShimLayout ⟨args, environ, false⟩ [] T ls ∧ Carried R 0 ls ∧
        (∀ e ∈ ls, WritesNative choiceShimLayout (wasiCap * 65536) e) ∧
        Linux.writeData 1 ls = committedWrites 1 T ∧
        ((∃ c, Exec (linuxHost arm64Flags choiceShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.exited c) w ∧ q.core.x 0 = c) ∨
          (Exec (linuxHost arm64Flags choiceShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped exitRejected) w ∧ q.core.x 0 = 1) ∨
          (Exec (linuxHost arm64Flags choiceShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped shimTrap) w ∧ q.core.x 0 = 2) ∨
          ((∃ residual,
              Prefix (linuxHost arm64Flags choiceShimLayout ⟨args, environ, false⟩ R)
                (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
                residual w) ∧ q.core.x 0 = 2)) := by
  have himp : command.module.imports = ABI.importsWith command.sysCalls := by
    rw [command.module, compile_imports_with]
  obtain ⟨q, rq, cq, x8q, ioq, hq⟩ :=
    wasiElf_footprint choice_elf_file
      (choice_elf_segments.trans choice_elf_layout.symm) himp calls_supported (by decide)
      choice_elf_room (fun I R => linux_footprint_native arm64Flags _ I R (by decide)) R p hl
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
theorem choice_elf_runs (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (small : stringsSize args + 8 * args.length ≤ Demos.RandomHistogram.argsLimit)
    (hl : ElfLoaded (byteAt choiceElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform choiceLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords choiceLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords choiceLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ T ls w, q.trace = ls.map A64.Event.sys ∧
        Images arm64Flags choiceShimLayout ⟨args, environ, false⟩ [] T ls ∧ Carried R 0 ls ∧
        ((∃ c, Exec (linuxHost arm64Flags choiceShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.exited c) w ∧ q.core.x 0 = c) ∨
          Exec (linuxHost arm64Flags choiceShimLayout ⟨args, environ, false⟩ R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped exitRejected) w ∨
          Exec (linuxHost arm64Flags choiceShimLayout ⟨args, environ, false⟩ R)
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
    wasiElf_footprint_with choice_elf_file
      (choice_elf_segments.trans choice_elf_layout.symm) himp calls_supported (by decide)
      choice_elf_room R p
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

/-- The random choice's corollary for `choice.elf`.  For every reply sequence `R`, a process
started as for `choice_elf` with arguments whose strings, each with its zero byte, and eight-byte
pointers take at most `argsLimit` bytes, 6 MiB, reaches `SVC #0` with X8 at 94, `exit_group`, and
the UART's state as it was.  Its trace holds the layer events `ls`, each of which holds its reply
of `R`, and when every `getrandom` of `ls` returned an error number or a count of at most its
length, positive for a positive length, and every `write` an error number or at most its count,
its third argument (`InRange`), X0 and `ls` meet `Choices`.  When `parseSpec` refuses N or K, no
layer event precedes `exit_group`, and X0 is 2.  Otherwise the layer events are groups that
mirror, one for one, WASI events that make the passes of `Rounds`, whose status is X0 and whose
random bytes are those that the groups of the passes' `random_get` calls that returned errno 0
returned.  Each pass is the group of a `random_get` of 4,096 bytes, `getrandom` calls with flags 0,
each for the bytes that the calls before it did not return, followed, when the group returned
errno 0, by `write` calls of descriptor 1, each of which offered the bytes of the pass's lines that
the writes before it did not take.  X0 is 0 only when the writes took the lines of the picks of the
first K accepted words of those bytes, and 77 only when those bytes hold the `512 · passes K` words
of the cap's passes, fewer than K of them accepted. -/
theorem choice_elf_choices (R : Linux.Replies) (p : Proc) {args environ : List (List UInt8)}
    {top : UInt64} (small : stringsSize args + 8 * args.length ≤ Demos.RandomHistogram.argsLimit)
    (hl : ElfLoaded (byteAt choiceElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform choiceLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords choiceLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords choiceLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ ls, q.trace = ls.map A64.Event.sys ∧ Carried R 0 ls ∧
        (Demos.RandomHistogram.InRange ls → Choices args ls (q.core.x 0)) := by
  obtain ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, himg, hcar, hend⟩ :=
    choice_elf_runs R p small hl hstack hpc htr
  refine ⟨q, rq, cq, x8q, ioq, ls, trq, hcar, fun range => ?_⟩
  have sized := Demos.RandomHistogram.carried_sized hcar
  rcases hend with ⟨c, h, hx⟩ | h | h
  · obtain ⟨c', exited, choices⟩ := linux_exec_choices small h himg range sized
    cases exited
    rw [hx]
    exact choices
  · obtain ⟨_, exited, -⟩ := linux_exec_choices small h himg range sized
    cases exited
  · obtain ⟨_, exited, -⟩ := linux_exec_choices small h himg range sized
    cases exited

/-! ## The premises hold together -/

/-- The initial stack of the arguments `witnessArgs` at `2^32`: `argc`, 3; the pointers to `c` at
`2^32 + 48`, to `1` at `2^32 + 50`, and to `1` at `2^32 + 52`; the zero words that end `argv` and
`envp`; and the strings `c`, `1`, and `1`, each with its zero byte. -/
def witnessStack : List UInt8 :=
  [3, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 1, 0, 0, 0, 50, 0, 0, 0, 1, 0, 0, 0,
    52, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    99, 0, 49, 0, 49, 0]

theorem witness_stack :
    InitialStack witnessArgs [] (2 ^ 32) ElfWitness.witnessTop (ElfWitness.stackMem witnessStack)
      where
  above := by decide
  below := by decide
  words := by decide
  argc := by decide +kernel
  argv := by
    intro i h
    unfold StringAt
    have : i = 0 ∨ i = 1 ∨ i = 2 := by
      simp only [witnessArgs, List.length_cons, List.length_nil] at h
      omega
    rcases this with rfl | rfl | rfl <;>
      simp only [witnessArgs, List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel
  argvEnd := by decide +kernel
  envp := fun _ h => absurd h (Nat.not_lt_zero _)
  envpEnd := by decide +kernel

/-- The premises of `choice_elf_choices` and `InRange` hold together.  For the replies
`witnessReplies`, the process `witnessProc`, the arguments `witnessArgs`, which give N and K of 1,
no environment, and the stack's top `witnessTop`, every premise of the corollary holds, and the
process reaches `exit_group` with X0 at 0 after layer events that hold their replies and meet
`InRange` and `Choices`. -/
theorem choice_elf_witness :
    ∃ (R : Linux.Replies) (p : Proc) (args environ : List (List UInt8)) (top : UInt64),
      argN args = 1 ∧ argK args = 1 ∧
      stringsSize args + 8 * args.length ≤ Demos.RandomHistogram.argsLimit ∧
      ElfLoaded (byteAt choiceElfBytes) p.core.mem ∧
      InitialStack args environ p.core.sp top p.core.mem ∧ p.core.pc = wasiEntry ∧
      p.trace = [] ∧
      ∃ q, ProcReachWith Linux.table R (wasiPlatform choiceLayout p.core.sp top)
          (fetchFrom p.core.mem elfEntry (elfWords choiceLayout)) p q ∧
        fetchFrom p.core.mem elfEntry (elfWords choiceLayout) q.core.pc = some svcWord ∧
        q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
        ∃ ls, q.trace = ls.map A64.Event.sys ∧ Carried R 0 ls ∧
          Demos.RandomHistogram.InRange ls ∧
          Choices args ls (q.core.x 0) ∧ q.core.x 0 = 0 := by
  have parsedN : argN witnessArgs = 1 := by decide +kernel
  have parsedK : argK witnessArgs = 1 := by decide +kernel
  have small : stringsSize witnessArgs + 8 * witnessArgs.length ≤
      Demos.RandomHistogram.argsLimit := by decide
  have loaded : ElfLoaded (byteAt choiceElfBytes)
      (ElfWitness.loadedMem (byteAt choiceElfBytes) 19916 4096 witnessStack) :=
    ElfWitness.loadedMem_loaded choice_elf_segments (by decide) (by decide)
  have stack := ElfWitness.loadedMem_initial (byteAt choiceElfBytes) 19916 4096 witness_stack
  refine ⟨witnessReplies,
    ElfWitness.witnessProc (ElfWitness.loadedMem (byteAt choiceElfBytes) 19916 4096 witnessStack),
    witnessArgs, [], ElfWitness.witnessTop, parsedN, parsedK, small, loaded, stack, rfl, rfl, ?_⟩
  obtain ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, himg, hcar, hend⟩ :=
    choice_elf_runs witnessReplies
      (ElfWitness.witnessProc
        (ElfWitness.loadedMem (byteAt choiceElfBytes) 19916 4096 witnessStack))
      small loaded stack rfl rfl
  refine ⟨q, rq, cq, x8q, ioq, ls, trq, hcar, ?_⟩
  rcases hend with ⟨c, h, hx⟩ | h | h
  · obtain ⟨exited, range⟩ := witness_run h himg hcar
    cases exited
    obtain ⟨c', exited, choices⟩ :=
      linux_exec_choices small h himg range (Demos.RandomHistogram.carried_sized hcar)
    cases exited
    exact ⟨range, by rw [hx]; exact choices, hx⟩
  · cases (witness_run h himg hcar).1
  · cases (witness_run h himg hcar).1

#print axioms choice_elf_file
#print axioms choice_elf_segments
#print axioms choice_elf_layout
#print axioms choice_elf_entry
#print axioms choice_elf_room
#print axioms choice_elf
#print axioms choice_elf_runs
#print axioms choice_elf_choices
#print axioms choice_elf_witness

end TestSupport.A64.ImageFilesRandomChoice
