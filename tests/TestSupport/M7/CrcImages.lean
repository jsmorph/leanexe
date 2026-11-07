import LeanExe.M7.Setup
import TestSupport.M7.Crc
import TestSupport.M7.Qemu

/-!
The image of the CRC-32 step `crcCmsdkTick`, function 5 of `crcCmsdkCompiled.module`, for QEMU's
`mps2-an500`, from the state `crcInit`, which no theorem covers.  The image holds the vector table
of `tests/TestSupport/M7/Qemu.lean`, the setup of the generator's area of `LeanExe/M7/Setup.lean`,
UART0's initialization, and the generator's program with the stack's limit at the area's end.
`m7-windows crc-qemu` writes it, and `tests/baremetal/m7-qemu.sh crc` runs it under QEMU against
`tests/baremetal/uart_crc.py`.
-/

namespace TestSupport.M7.CrcImages

open LeanExe.M7 TestSupport.M7.Crc

/-- The image's layout: QEMU's vector table and SP, and the setup of the area before UART0's
initialization. -/
def boot : Boot := Qemu.boot.setup (setupCode areaHeader areaPages crcCmsdkCompiled.module)

/-- The image's instructions from the self-loop on. -/
def program : GenM (List Instr) :=
  bootProgram boot crcCmsdkCompiled.module 5 [crcInit] areaEnd Qemu.devBase

/-- The bytes of the image. -/
def image : GenM (List UInt8) := do
  return bootBytes boot (← program)

/-- The address of the loop's head of `main`. -/
def loopHead : UInt32 := after boot.base (mainStart [crcInit])

end TestSupport.M7.CrcImages
