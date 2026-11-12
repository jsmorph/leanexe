import TestSupport.A64.FlipElf
import LeanExe.A64.File

/-!
The theorems of the Linux executable that `a64-elf emit` writes for `flip`, a function over bytes
that reads standard input and writes standard output.  `tests/linux/a64-elf.sh` elaborates this
file in the directory of the executable, so `file_nat%` and `file_size%` read flip.elf, and no
build target includes it.  The kernel evaluates `genSysElf` on `flip`'s entry of
`Flip.compiled.module`, `inMax`, the stack's room, and the cap, and checks that the executable's
bytes are the file's (`flip_elf_file`).  `flip_elf_segments` states the two program headers that
`elfSegments` reads from the file, the premise of `ElfLoaded`: the text segment at 0x400000,
readable and executable, and the data segment at 0x410000, readable and writable, whose memory
size exceeds its file size by the zeros of the area and the stack.  `flip_elf_entry` states that
the file's entry is `elfEntry`.  From a process whose memory holds the file as Linux's loader
places it, with the program counter at the entry and no event in the trace, for a kernel none of
whose calls fails, `flip_elf` states that when standard input holds at most `inMax` bytes the
process reaches `SVC #0` with X8 at 94, `exit_group`, and X0 at 0, after it wrote to standard
output the input with bit 5 of each byte flipped, and `flip_elf_over` that for a longer input it
reaches it with X0 at 64 and nothing written.  Both leave the UART's state as it was.
-/

namespace TestSupport.A64.ImageFilesFlipElf

open LeanExe.A64 TestSupport.A64 TestSupport.A64.Flip TestSupport.A64.FlipElf

def flipElfBytes : Nat := file_nat% "flip.elf"
def flipElfSize : Nat := file_size% "flip.elf"

/-- The executable's layout. -/
def flipLayout : ElfLayout := elfLayout compiled.module entry inMax room flipCap

set_option maxRecDepth 100000

theorem flip_elf_file : bytesOk (genSysElf compiled.module entry inMax room flipCap)
    flipElfBytes flipElfSize = true := by decide +kernel

theorem flip_elf_segments : elfSegments (byteAt flipElfBytes) =
    [⟨1, 5, 0, 0x400000, 3424, 3424⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 18157584⟩] := by
  decide +kernel

theorem flip_elf_layout : elfSegmentsOf flipLayout =
    [⟨1, 5, 0, 0x400000, 3424, 3424⟩, ⟨1, 6, 0x10000, 0x410000, 4096, 18157584⟩] := by
  decide +kernel

theorem flip_elf_entry : elfEntryOf (byteAt flipElfBytes) = elfEntry.toNat := by decide +kernel

theorem flip_elf (K : Kernel) (p : Proc) (hl : ElfLoaded (byteAt flipElfBytes) p.core.mem)
    (hpc : p.core.pc = elfEntry) (htr : p.trace = []) (hok : ∀ k, K.fail k = none)
    (hlen : K.input.length ≤ inMax.toNat) :
    ∃ p', ProcReach K (elfPlatform flipLayout)
        (fetchFrom p.core.mem elfEntry (elfWords flipLayout)) p p' ∧
      fetchFrom p.core.mem elfEntry (elfWords flipLayout) p'.core.pc = some svcWord ∧
      p'.core.x 8 = 94 ∧ p'.core.x 0 = 0 ∧ stdoutOf p'.trace = K.input.map (· ^^^ 32) ∧
      p'.core.io = p.core.io := by
  obtain ⟨p', r, c, x8, out, io⟩ := (elf_bytes_run flip_elf_file
    (flip_elf_segments.trans flip_elf_layout.symm) (by decide) (by decide) flip_elf_runs K p hl
    hpc htr hok).1 hlen
  rcases out with ⟨x0, o⟩ | ⟨hf, -⟩
  · exact ⟨p', r, c, x8, x0, o, io⟩
  · exact hf.elim

theorem flip_elf_over (K : Kernel) (p : Proc) (hl : ElfLoaded (byteAt flipElfBytes) p.core.mem)
    (hpc : p.core.pc = elfEntry) (htr : p.trace = []) (hok : ∀ k, K.fail k = none)
    (hlen : inMax.toNat < K.input.length) :
    ∃ p', ProcReach K (elfPlatform flipLayout)
        (fetchFrom p.core.mem elfEntry (elfWords flipLayout)) p p' ∧
      fetchFrom p.core.mem elfEntry (elfWords flipLayout) p'.core.pc = some svcWord ∧
      p'.core.x 8 = 94 ∧ p'.core.x 0 = 64 ∧ stdoutOf p'.trace = [] ∧
      p'.core.io = p.core.io :=
  (elf_bytes_run flip_elf_file (flip_elf_segments.trans flip_elf_layout.symm) (by decide)
    (by decide) flip_elf_runs K p hl hpc htr hok).2 hlen

#print axioms flip_elf_file
#print axioms flip_elf_segments
#print axioms flip_elf_entry
#print axioms flip_elf
#print axioms flip_elf_over

end TestSupport.A64.ImageFilesFlipElf
