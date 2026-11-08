import LeanExe.M7.Board
import TestSupport.M7.Qemu
import TestSupport.M7.Signed

/-!
The images of the signed step of `tests/TestSupport/M7/Signed.lean`, both from the state
`sgInit`: the program of `sgUsart3Tick`, function 4 of `sgCompiled.module`, for the NUCLEO-F767ZI
in the layout of `LeanExe/M7/Board.lean`, and the program of `sgCmsdkTick`, function 5, for QEMU's
`mps2-an500` in the layout of `tests/TestSupport/M7/Qemu.lean`.  `m7-windows signed-board` writes
the first to `signed.bin`, which `st-flash` writes to the board's flash at `0x08000000`, and
`m7-windows signed-qemu` writes the second to `signed-cmsdk-qemu.bin`.
-/

namespace TestSupport.M7.Signed

open LeanExe.M7

/-- The words of the initial state. -/
abbrev sgState : List UInt64 := sgWords sgInit

/-- The board's image from the self-loop on. -/
def boardProgram : GenM (List Instr) := LeanExe.M7.Nucleo.program sgCompiled.module 4 sgState

/-- The bytes of the board's image. -/
def boardImage : GenM (List UInt8) := LeanExe.M7.Nucleo.image sgCompiled.module 4 sgState

/-- The address of the loop's head of `main` in the board's image. -/
def boardHead : UInt32 := LeanExe.M7.Nucleo.loopHead sgState

/-- QEMU's image from the self-loop on. -/
def qemuProgram : GenM (List Instr) :=
  bootProgram Qemu.boot sgCompiled.module 5 sgState Qemu.stackLimit Qemu.devBase

/-- The bytes of QEMU's image. -/
def qemuImage : GenM (List UInt8) := do
  return bootBytes Qemu.boot (← qemuProgram)

/-- The address of the loop's head of `main` in QEMU's image. -/
def qemuHead : UInt32 := after Qemu.boot.base (mainStart sgState)

end TestSupport.M7.Signed
