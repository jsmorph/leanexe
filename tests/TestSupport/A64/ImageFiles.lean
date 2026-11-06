import TestSupport.A64.Programs
import LeanExe.A64.File

/-!
The kernel's check of the arm64 Images that `a64-programs emit` writes.
`tests/baremetal/a64-images.sh` elaborates this file in the directory of those files after it emits
them, so `file_nat%` and `file_size%` read each NAME.img, and no build target includes it.  For each
program the kernel evaluates `genImage` on the program's module, entry, arguments, stack, cap, and
form of result at `imageBase`, and checks that the image's bytes are the file's.
-/

namespace TestSupport.A64.ImageFiles

open LeanExe.A64 TestSupport.A64

set_option maxRecDepth 100000

theorem gcd : bytesOk (genImage TestSupport.Native.Gcd.loopCompiled.module 2 [1071, 462] room cap
    .word imageBase) (file_nat% "gcd.img") (file_size% "gcd.img") = true := by decide +kernel

theorem gcdrec : bytesOk (genImage TestSupport.Native.Gcd.recCompiled.module 3 [1071, 462] room
    cap .word imageBase) (file_nat% "gcdrec.img") (file_size% "gcdrec.img") = true := by
  decide +kernel

theorem crc32 : bytesOk (genImage TestSupport.Bare.crcCompiled.module 5
    [0x3837363534333231, 0x39] room cap .word imageBase) (file_nat% "crc32.img")
    (file_size% "crc32.img") = true := by decide +kernel

theorem sha256 : bytesOk (genImage TestSupport.Bare.shaCompiled.module 11 [0x636261] room cap
    .array imageBase) (file_nat% "sha256.img") (file_size% "sha256.img") = true := by
  decide +kernel

theorem depth : bytesOk (genImage Verified.Examples.Fold.compiled.module 13 [1000] room cap .word
    imageBase) (file_nat% "depth.img") (file_size% "depth.img") = true := by decide +kernel

end TestSupport.A64.ImageFiles

#print axioms TestSupport.A64.ImageFiles.gcd
#print axioms TestSupport.A64.ImageFiles.gcdrec
#print axioms TestSupport.A64.ImageFiles.crc32
#print axioms TestSupport.A64.ImageFiles.sha256
#print axioms TestSupport.A64.ImageFiles.depth
