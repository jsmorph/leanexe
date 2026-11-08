import LeanExe.M7.Board
import LeanExe.M7.Setup
import TestSupport.M7.Crc
import TestSupport.M7.Qemu

/-!
The images of the CRC-32 step through the Cortex-M7 back end, both from the state `crcInit`: the
program of `crcUsart3Tick`, function 5 of `crcStepCompiled.module`, for the NUCLEO-F767ZI in the
layout `areaBoot` of `LeanExe/M7/Board.lean`, and the program of `crcCmsdkTick`, function 5 of
`crcCmsdkCompiled.module`, for QEMU's `mps2-an500` in the layout of
`tests/TestSupport/M7/Qemu.lean`.  Each image runs the setup of the generator's area of
`LeanExe/M7/Setup.lean` before its initialization, which clears the area and writes the nonzero
words of its first bytes, among them CRC-32's table at the memory's byte 4096, and the stack's
limit lies at the area's end.  `m7-windows crc-board` writes the first to `crc.bin`, which
`st-flash` writes to the board's flash at `0x08000000`, and `m7-windows crc-qemu` writes the
second to `crc-cmsdk-qemu.bin`, which `tests/baremetal/m7-qemu.sh crc` runs under QEMU against
`tests/baremetal/uart_crc.py`.
-/

namespace TestSupport.M7.CrcImages

open LeanExe.M7 TestSupport.M7.Crc

/-- The board's layout: `areaBoot` of `LeanExe/M7/Board.lean`, the board's vector table and SP,
and the setup of the area before the board's initialization. -/
def boardBoot : Boot := Nucleo.areaBoot crcStepCompiled.module

/-- The board's image from the self-loop on. -/
def boardProgram : GenM (List Instr) :=
  bootProgram boardBoot crcStepCompiled.module 5 [crcInit] areaEnd Nucleo.devBase

/-- The bytes of the board's image. -/
def boardImage : GenM (List UInt8) := do
  return bootBytes boardBoot (← boardProgram)

/-- The address of the loop's head of `main` in the board's image. -/
def boardHead : UInt32 := Nucleo.areaLoopHead crcStepCompiled.module [crcInit]

/-- QEMU's layout: QEMU's vector table and SP, and the setup of the area before UART0's
initialization. -/
def qemuBoot : Boot := Qemu.boot.setup (setupCode areaHeader areaPages crcCmsdkCompiled.module)

/-- QEMU's image from the self-loop on. -/
def qemuProgram : GenM (List Instr) :=
  bootProgram qemuBoot crcCmsdkCompiled.module 5 [crcInit] areaEnd Qemu.devBase

/-- The bytes of QEMU's image. -/
def qemuImage : GenM (List UInt8) := do
  return bootBytes qemuBoot (← qemuProgram)

/-- The address of the loop's head of `main` in QEMU's image. -/
def qemuHead : UInt32 := after qemuBoot.base (mainStart [crcInit])

end TestSupport.M7.CrcImages
