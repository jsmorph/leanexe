import TestSupport.M7.Windows

/-!
The kernel's check of the code of the SHA-256 step for USART3 that `m7-windows image sha-usart3`
writes.  `tests/baremetal/m7-image.sh` elaborates this file in the directory of that file, so
`file_nat%` and `file_size%` read it, and no build target includes it.  The kernel evaluates
`genProgram` on `shaUsart3Tick`'s module and index, the words of `shaInit`, the code's base, the
stack's limit at the area's end, the device window, and the code of `udivmod64`, and checks that
the file's bytes are those of the generated instructions.  No theorem states the behavior of these
instructions, since the simulation does not cover the forms of `compress`'s loop.
-/

namespace TestSupport.M7.ShaImageFile

open LeanExe.M7 TestSupport.M7.Windows TestSupport.M7.Sha

def shaBytes : Nat := file_nat% "sha-usart3.bin"
def shaSize : Nat := file_size% "sha-usart3.bin"

/-- The file holds the bytes of the SHA-256 step's generated program. -/
theorem sha_file :
    fileOk (genProgram shaStepCompiled.module 13 (shaWords shaInit) codeBase areaEnd devBase
      udivmod64) shaBytes shaSize = true := by
  decide +kernel

/-- The instructions whose bytes the file holds. -/
theorem sha_image : ∃ is, genProgram shaStepCompiled.module 13 (shaWords shaInit) codeBase
    areaEnd devBase udivmod64 = .ok is ∧ LeanExe.FileNat.natOfBytes (imageBytes is) = shaBytes ∧
    (imageBytes is).length = shaSize :=
  fileOk_ok sha_file

end TestSupport.M7.ShaImageFile

#print axioms TestSupport.M7.ShaImageFile.sha_image
