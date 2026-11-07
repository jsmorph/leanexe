import TestSupport.M7.Step
import TestSupport.M7.Windows

/-!
The kernel's check of the code of the echo for USART3 that `m7-windows image echo-usart3` writes.
`tests/baremetal/m7-image.sh` elaborates this file in the directory of that file, so `file_nat%`
and `file_size%` read it, and no build target includes it.  The kernel evaluates `genProgram` on
`usart3Tick`'s module and index, the initial state 3, the code's base, the stack's limit, the
device window, and the code of `udivmod64`, and checks that the file's bytes are those of the
generated instructions.  The instructions are those of which `usart3_step` states the call of the
step.
-/

namespace TestSupport.M7.ImageFile

open LeanExe.M7 TestSupport.M7.Windows TestSupport.Bare

def echoBytes : Nat := file_nat% "echo-usart3.bin"
def echoSize : Nat := file_size% "echo-usart3.bin"

/-- The file holds the bytes of the echo's generated program. -/
theorem echo_file :
    fileOk (genProgram reqCompiled.module 9 [3] codeBase stackLimit devBase udivmod64) echoBytes
      echoSize = true := by
  decide +kernel

/-- The instructions whose bytes the file holds, for which `usart3_step` holds at `codeBase`. -/
theorem echo_image : ∃ is, genProgram reqCompiled.module 9 [3] codeBase stackLimit devBase
    udivmod64 = .ok is ∧ LeanExe.FileNat.natOfBytes (imageBytes is) = echoBytes ∧
    (imageBytes is).length = echoSize :=
  fileOk_ok echo_file

end TestSupport.M7.ImageFile

#print axioms TestSupport.M7.ImageFile.echo_image
#print axioms TestSupport.M7.usart3_step
#print axioms TestSupport.M7.cmsdk_step
#print axioms TestSupport.M7.echo_stack
#print axioms LeanExe.M7.step_call
