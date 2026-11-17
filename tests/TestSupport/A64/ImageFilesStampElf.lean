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

#print axioms stamp_elf_file
#print axioms stamp_elf_segments
#print axioms stamp_elf_layout
#print axioms stamp_elf_entry

end TestSupport.A64.ImageFilesStampElf
