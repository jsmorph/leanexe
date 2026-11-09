import LeanExe.M7.Board
import TestSupport.M7.Qemu
import Demos.Bms.Compiled

/-!
The images of the BMS step of `Demos/Bms/Program.lean`, both from the state `bmsInit`: the
program of `bmsTickUsart3`, function 56 of `bmsCompiled.module`, for the NUCLEO-F767ZI in the
layout `bootWith initOvrdis` of `LeanExe/M7/Board.lean`, whose initialization also writes
`OVRDIS` to `USART_CR3`, and the program of `bmsTick`, function 57, for QEMU's `mps2-an500` in the
layout of `tests/TestSupport/M7/Qemu.lean`.  With `OVRDIS` set, a byte that arrives while
`USART_RDR` holds another replaces it and reception continues, so the next `0x00` restores the
framing's alignment after an overrun.  `m7-windows bms-board` writes the first to `bms.bin`,
which `st-flash` writes to the board's flash at `0x08000000`, and `m7-windows bms-qemu` writes the
second to `bms-cmsdk-qemu.bin`.
-/

namespace TestSupport.M7.Bms

open LeanExe.M7 Demos.Bms.Program

/-- The words of the initial state. -/
abbrev bmsState : List UInt64 := bmsWords bmsInit

/-- The board's image from the self-loop on, with the initialization `initOvrdis`. -/
def boardProgram : GenM (List Instr) :=
  Nucleo.programWith Nucleo.initOvrdis bmsCompiled.module 56 bmsState

/-- The bytes of the board's image. -/
def boardImage : GenM (List UInt8) :=
  Nucleo.imageWith Nucleo.initOvrdis bmsCompiled.module 56 bmsState

/-- The address of the loop's head of `main` in the board's image. -/
def boardHead : UInt32 := Nucleo.loopHeadWith Nucleo.initOvrdis bmsState

/-- QEMU's image from the self-loop on. -/
def qemuProgram : GenM (List Instr) :=
  bootProgram Qemu.boot bmsCompiled.module 57 bmsState Qemu.stackLimit Qemu.devBase

/-- The bytes of QEMU's image. -/
def qemuImage : GenM (List UInt8) := do
  return bootBytes Qemu.boot (← qemuProgram)

/-- The address of the loop's head of `main` in QEMU's image. -/
def qemuHead : UInt32 := after Qemu.boot.base (mainStart bmsState)

end TestSupport.M7.Bms
