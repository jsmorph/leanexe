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
the generator's layout.  `readall_elf_entry` states that the file's entry is the prefix
`wasiEntry`, and `readall_elf_room` that the stack's room holds the module's stack bound.

`readall_elf` holds for every choice of open flags `F`, launch `I`, and reply sequence.  From a
process whose memory holds the file as Linux's loader places it, with the arguments `args` and the
environment `environ` on Linux's initial stack at SP, the program counter at the entry, and no
event in the trace, the process reaches `SVC #0` with X8 at 94, `exit_group`, with the UART's state
as it was.  Its trace holds the layer events `ls`, the images of the WASI events `T` of a run of
the command's action under `linuxHost`, each of which holds its reply and has its output region
within the cap's linear memory.  The reads of descriptor 0 in `ls` returned the bytes that the
`fd_read` events of `T` committed, and its writes of descriptor 1 took the bytes that the
`fd_write` events of `T` to standard output committed.  `T` is the trace of an `Exec` run that
ends at an accepted exit, whose status X0 holds, at an exit that the shim rejects, with X0 at 1,
or at a trap of the shim, with X0 at 2, or of a `Prefix` run of the action, with X0 at 2.
`wasiElf_footprint` gives these facts
for arm64's open flags and the launch `⟨args, environ, false⟩`.  The command's action makes no
flat call (`main_streams`), so its trace holds none, its layer events are reads and writes, whose
output regions lie in linear memory, and its images and its runs under `linuxHost` hold for every
choice of open flags and launch (`Images.streams`, `Exec.streams`, `Prefix.streams`).

`readall_elf_message` is readAll's message corollary for the file, for every reply sequence of the
class `Steady` of `Verified/Examples/WasiReadAllSteady.lean`, which answers each read with a result
of at most its capacity and each write of `n` bytes with a result of at most `n` and at least 1.
The process reaches `exit_group` with X0 at `statusOf` of the bytes that its reads of descriptor 0
returned, and its layer events meet `Copies`.  `wasiElf_footprint_with` gives the run from
`linux_footprint_budget`, the footprint at the executable's cap of 4,096 pages without a guest trap
under every reply sequence, and `linux_exec_succeeded` gives the status and `Copies` from the
`Exec` run that the footprint names, whose WASI events succeed under the class
(`succeeded_of_steady`).
-/

namespace TestSupport.A64.ImageFilesWasiElf

open LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim Verified.ShimA64
  Verified.Examples.WasiReadAll TestSupport.A64.WasiElf

def readAllElfBytes : Nat := file_nat% "readall.elf"
def readAllElfSize : Nat := file_size% "readall.elf"

/-- The executable's layout. -/
def readAllLayout : ElfLayout := wasiLayout command.module readAllStart wasiRoom wasiCap

/-- The shim's layout of the executable. -/
def readAllShimLayout : ShimLayout := wasiShimLayout command.module readAllStart wasiRoom wasiCap

set_option maxRecDepth 100000

theorem readall_elf_file : bytesOk (genWasiElf command.module readAllStart wasiRoom wasiCap)
    readAllElfBytes readAllElfSize = true := by decide +kernel

theorem readall_elf_segments : elfSegments (byteAt readAllElfBytes) =
    [⟨1, 5, 0, 0x400000, 10684, 10684⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem readall_elf_layout : elfSegmentsOf readAllLayout =
    [⟨1, 5, 0, 0x400000, 10684, 10684⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 268510288⟩] := by
  decide +kernel

theorem readall_elf_entry : elfEntryOf (byteAt readAllElfBytes) = wasiEntry.toNat := by
  decide +kernel

theorem readall_elf_room : wasiStackBound command.module readAllStart ≤ wasiRoom.toNat := by
  decide +kernel

theorem readall_elf (F : OpenFlags) (I : Launch) (R : Linux.Replies) (p : Proc)
    {args environ : List (List UInt8)} {top : UInt64}
    (hl : ElfLoaded (byteAt readAllElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform readAllLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords readAllLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords readAllLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ T ls w, q.trace = ls.map A64.Event.sys ∧
        Images F readAllShimLayout I [] T ls ∧ Carried R 0 ls ∧
        (∀ e ∈ ls, WritesLinear readAllShimLayout (wasiCap * 65536) e) ∧
        Linux.readData 0 ls = committedReads 0 T ∧
        Linux.writeData 1 ls = committedWrites 1 T ∧
        ((∃ c, Exec (linuxHost F readAllShimLayout I R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.exited c) w ∧ q.core.x 0 = c) ∨
          (Exec (linuxHost F readAllShimLayout I R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped exitRejected) w ∧ q.core.x 0 = 1) ∨
          (Exec (linuxHost F readAllShimLayout I R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            (.trapped shimTrap) w ∧ q.core.x 0 = 2) ∨
          ((∃ residual, Prefix (linuxHost F readAllShimLayout I R)
            (main.bind fun status => Action.exit (α := Unit) status) nativeWorld.world T
            residual w) ∧ q.core.x 0 = 2)) := by
  have himp : command.module.imports = ABI.importsWith [] := by
    rw [command.module, compile_imports]
    rfl
  obtain ⟨q, rq, cq, x8q, ioq, hq⟩ :=
    wasiElf_footprint (calls := []) readall_elf_file
      (readall_elf_segments.trans readall_elf_layout.symm) himp (fun _ h => nomatch h)
      (by decide) readall_elf_room
      (fun I R => linux_footprint_native arm64Flags _ I R (by decide)) R p hl hstack hpc htr
  have hsu : startup (needsCheck (command.module.imports.drop 3))
      (wasiScratch command.module readAllStart wasiRoom wasiCap) R = ([], some false) := by
    rw [himp]
    rfl
  rw [hsu] at hq
  obtain ⟨T, ls, w, trq, himg, hcar, hwq, hend⟩ := hq
  rw [List.nil_append] at trq
  have hR : (fun j => R (([] : List Linux.Event).length + j)) = R := funext fun j => by simp
  rw [hR] at hend
  have hT : StreamTrace T := by
    rcases hend with ⟨_, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨_, h⟩, -⟩
    · exact Exec.streamTrace h main_streams
    · exact Exec.streamTrace h main_streams
    · exact Exec.streamTrace h main_streams
    · exact Prefix.streamTrace h main_streams
  refine ⟨q, rq, cq, x8q, ioq, T, ls, w, trq, Images.streams himg hT [], hcar,
    fun e he => (hwq e he).linear ?_, himg.readData 0, himg.writeData 1, ?_⟩
  · rcases Images.streamCalls himg hT e he with h | h <;> rw [h] <;> decide
  rcases hend with ⟨c, h, hx⟩ | ⟨h, hx⟩ | ⟨h, hx⟩ | ⟨-, ⟨residual, h⟩, hx⟩
  · exact .inl ⟨c, Exec.streams rfl rfl h hT, hx⟩
  · exact .inr (.inl ⟨Exec.streams rfl rfl h hT, hx⟩)
  · exact .inr (.inr (.inl ⟨Exec.streams rfl rfl h hT, hx⟩))
  · exact .inr (.inr (.inr ⟨⟨residual, Prefix.streams rfl rfl h hT⟩, hx⟩))

/-- readAll's message corollary for `readall.elf`.  For every choice of open flags `F`, launch `I`,
and reply sequence `R` of the class `Steady F readAllShimLayout I R`, which answers each read with
a result of at most its capacity and each write of `n` bytes with a result of at most `n` and at
least 1, a process started as for `readall_elf` reaches `SVC #0` with X8 at 94, `exit_group`, and
the UART's state as it was.  Its trace holds the layer events `ls`, each of which holds its reply
of `R`, X0 holds `statusOf (Linux.readData 0 ls)`, 0 when the reads of
descriptor 0 returned at most `limit`, 1,000,000, bytes and 1 otherwise, and `ls` meets `Copies`:
reads of 4,096 bytes from descriptor 0, each but the last returning bytes, at most `limit` bytes
before the last read and `limit + 4096` in all, the last read returning none unless the bytes
exceed `limit`, followed by writes of descriptor 1 that took the bytes that the reads returned.
The class holds Linux's replies when standard input is a regular file or a pipe and standard
output a regular file or a pipe and no call fails, since such a write takes at least one byte.  It
excludes every reply that reports an error, every result outside the request's range, and every
write that returns 0. -/
theorem readall_elf_message (F : OpenFlags) (I : Launch) (R : Linux.Replies) (p : Proc)
    {args environ : List (List UInt8)} {top : UInt64}
    (steady : Steady F readAllShimLayout I R)
    (hl : ElfLoaded (byteAt readAllElfBytes) p.core.mem)
    (hstack : InitialStack args environ p.core.sp top p.core.mem)
    (hpc : p.core.pc = wasiEntry) (htr : p.trace = []) :
    ∃ q, ProcReachWith Linux.table R (wasiPlatform readAllLayout p.core.sp top)
        (fetchFrom p.core.mem elfEntry (elfWords readAllLayout)) p q ∧
      fetchFrom p.core.mem elfEntry (elfWords readAllLayout) q.core.pc = some svcWord ∧
      q.core.x 8 = 94 ∧ q.core.io = p.core.io ∧
      ∃ ls, q.trace = ls.map A64.Event.sys ∧ Carried R 0 ls ∧
        q.core.x 0 = statusOf (Linux.readData 0 ls) ∧ Copies ls := by
  have native : Steady arm64Flags readAllShimLayout ⟨args, environ, false⟩ R :=
    steady.streams
  have himp : command.module.imports = ABI.importsWith [] := by
    rw [command.module, compile_imports]
    rfl
  have hsu : startup (needsCheck (command.module.imports.drop 3))
      (wasiScratch command.module readAllStart wasiRoom wasiCap) R = ([], some false) := by
    rw [himp]
    rfl
  have hR : (fun j => R (([] : List Linux.Event).length + j)) = R := funext fun j => by simp
  obtain ⟨q, rq, cq, x8q, ioq, hq⟩ :=
    wasiElf_footprint_with (calls := []) readall_elf_file
      (readall_elf_segments.trans readall_elf_layout.symm) himp (fun _ h => nomatch h)
      (by decide) readall_elf_room R p
      (fun l₀ granted h => by
        rw [hsu] at h
        cases h
        rw [hR]
        exact linux_footprint_budget arm64Flags _ ⟨args, environ, false⟩ R (by decide)
          (by decide))
      hl hstack hpc htr
  rw [hsu] at hq
  obtain ⟨T, ls, w, trq, himg, hcar, -, hend⟩ := hq
  rw [List.nil_append] at trq
  rw [hR] at hend
  have safe : SteadyAlong _ _ _ := native.along
  refine ⟨q, rq, cq, x8q, ioq, ls, trq, hcar, ?_⟩
  rcases hend with ⟨c, h, hx⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨impossible, -⟩
  · obtain ⟨exited, copies⟩ := linux_exec_succeeded h himg (succeeded_of_steady h safe)
    exact ⟨by rw [hx]; exact Outcome.exited.inj exited, copies⟩
  · cases (linux_exec_succeeded h himg (succeeded_of_steady h safe)).1
  · cases (linux_exec_succeeded h himg (succeeded_of_steady h safe)).1
  · cases impossible

#print axioms readall_elf_file
#print axioms readall_elf_segments
#print axioms readall_elf_layout
#print axioms readall_elf_entry
#print axioms readall_elf_room
#print axioms readall_elf
#print axioms readall_elf_message

end TestSupport.A64.ImageFilesWasiElf
