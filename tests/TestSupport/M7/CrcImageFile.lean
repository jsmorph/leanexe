import TestSupport.M7.CrcStep
import TestSupport.M7.Windows

/-!
The kernel's check of the code of the CRC-32 step for USART3 that `m7-windows image crc-usart3`
writes.  `tests/baremetal/m7-image.sh` elaborates this file in the directory of that file, so
`file_nat%` and `file_size%` read it, and no build target includes it.  The kernel evaluates
`genProgram` on `crcUsart3Tick`'s module and index, the initial state `crcInit`, the code's base,
the stack's limit at the area's end, the device window, and the code of `udivmod64`, and checks
that the file's bytes are those of the generated instructions.  The instructions are those of
which `crc_step` states the call of the step.
-/

namespace TestSupport.M7.CrcImageFile

open LeanExe.M7 TestSupport.M7.Windows TestSupport.M7.Crc

def crcBytes : Nat := file_nat% "crc-usart3.bin"
def crcSize : Nat := file_size% "crc-usart3.bin"

/-- The file holds the bytes of the CRC-32 step's generated program. -/
theorem crc_file :
    fileOk (genProgram crcStepCompiled.module 5 [crcInit] codeBase areaEnd devBase udivmod64)
      crcBytes crcSize = true := by
  decide +kernel

/-- The instructions whose bytes the file holds. -/
theorem crc_image : ∃ is, genProgram crcStepCompiled.module 5 [crcInit] codeBase areaEnd devBase
    udivmod64 = .ok is ∧ LeanExe.FileNat.natOfBytes (imageBytes is) = crcBytes ∧
    (imageBytes is).length = crcSize :=
  fileOk_ok crc_file

end TestSupport.M7.CrcImageFile

#print axioms TestSupport.M7.CrcImageFile.crc_image
#print axioms TestSupport.M7.crc_step
#print axioms TestSupport.M7.crcCmsdk_step
#print axioms TestSupport.M7.crc_stack
#print axioms LeanExe.M7.step_call
