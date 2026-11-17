import TestSupport.A64.StampElf
import LeanExe.A64.File
import LeanExe.A64.Proof.StampImage

/-!
The theorems of the stamp executable that `a64-elf emit` writes for `flipBit5`, which reads the
file `stamp.in` and writes `stamp.out`.  `tests/linux/a64-elf.sh` elaborates this file in the
directory of the executable, so `file_nat%` and `file_size%` read stamp.elf, and no build target
includes it.  The kernel evaluates `genStampElf` on `flip`'s entry of `Flip.compiled.module`,
`stampInMax`, the stack's room, the cap, and the two paths, and checks that the executable's bytes
are the file's (`stamp_elf_file`).  `stamp_elf_segments` states the two program headers that
`elfSegments` reads from the file, the premise of `ElfLoaded`: the text segment at 0x400000,
readable and executable, and the data segment at 0x410000, readable and writable, whose memory
size exceeds its file size by the zeros of the area and the stack.  `stamp_elf_layout` states that
`stampLayout` gives the same headers, and `stamp_elf_entry` that the file's entry is `elfEntry`.

`stamp_elf_any` covers every record of the kernel's replies.  From a process whose memory holds
the file as Linux's loader places it, with the program counter at the entry and no event in the
trace, a run in which every `SVC #0` takes the Linux call layer's rule for a call of
`LeanExe.Linux.table` reaches `SVC #0` with X8 at 94, `exit_group`, with the UART's state as it
was and only the layer's events in its trace.  Those events are the ones of `StampEvents` for the
flip function and no trap: X0 holds 0 and the bytes written to `stamp.out` are the clock's 16
bytes, the 16 random bytes, and the bytes read from `stamp.in`, each with bit 5 flipped, or X0
holds the status of the call that failed, after the events up to that call.
-/

namespace TestSupport.A64.ImageFilesStampElf

open LeanExe.A64 TestSupport.A64 TestSupport.A64.Flip TestSupport.A64.StampElf

def stampElfBytes : Nat := file_nat% "stamp.elf"
def stampElfSize : Nat := file_size% "stamp.elf"

/-- The executable's layout. -/
def stampElfLayout : ElfLayout :=
  stampLayout compiled.module entry stampInMax room flipCap inPath outPath

set_option maxRecDepth 100000

theorem stamp_elf_file : bytesOk (genStampElf compiled.module entry stampInMax room flipCap inPath
    outPath) stampElfBytes stampElfSize = true := by decide +kernel

theorem stamp_elf_segments : elfSegments (byteAt stampElfBytes) =
    [⟨1, 5, 0, 0x400000, 3864, 3864⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 18157632⟩] := by
  decide +kernel

theorem stamp_elf_layout : elfSegmentsOf stampElfLayout =
    [⟨1, 5, 0, 0x400000, 3864, 3864⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 18157632⟩] := by
  decide +kernel

theorem stamp_elf_entry : elfEntryOf (byteAt stampElfBytes) = elfEntry.toNat := by decide +kernel

theorem stamp_elf_any (R : LeanExe.Linux.Replies) (p : Proc)
    (hl : ElfLoaded (byteAt stampElfBytes) p.core.mem) (hpc : p.core.pc = elfEntry)
    (htr : p.trace = []) :
    ∃ p', ProcReachWith LeanExe.Linux.table R (elfPlatform stampElfLayout)
        (fetchFrom p.core.mem elfEntry (elfWords stampElfLayout)) p p' ∧
      fetchFrom p.core.mem elfEntry (elfWords stampElfLayout) p'.core.pc = some svcWord ∧
      p'.core.x 8 = 94 ∧ p'.core.io = p.core.io ∧
      p'.trace = (sysEvents p'.trace).map Event.sys ∧
      ∃ sp : UInt64,
        (p'.core.x 0 = 0 ∧ StampEvents sp stampInMax inPath outPath (fun D => D.map (· ^^^ 32))
          (fun _ _ => False) none (sysEvents p'.trace)) ∨
        StampEvents sp stampInMax inPath outPath (fun D => D.map (· ^^^ 32)) (fun _ _ => False)
          (some (p'.core.x 0)) (sysEvents p'.trace) :=
  stamp_bytes_run_any stamp_elf_file (stamp_elf_segments.trans stamp_elf_layout.symm)
    (by decide) stamp_elf_runs_any R p hl hpc htr

#print axioms stamp_elf_file
#print axioms stamp_elf_segments
#print axioms stamp_elf_layout
#print axioms stamp_elf_entry
#print axioms stamp_elf_any

end TestSupport.A64.ImageFilesStampElf
