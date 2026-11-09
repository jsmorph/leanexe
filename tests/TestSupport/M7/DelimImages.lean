import LeanExe.M7.Board
import TestSupport.M7.Qemu
import TestSupport.M7.Delim

/-!
The images of the echo of records of `tests/TestSupport/M7/Delim.lean`, both from the state
`dlInit`: the program of `dlUsart3Tick`, function 22 of `dlCompiled.module`, for the
NUCLEO-F767ZI in the layout `bootWith initOvrdis` of `LeanExe/M7/Board.lean`, whose
initialization also writes `OVRDIS` to `USART_CR3`, and the program of `dlCmsdkTick`, function
23, for QEMU's `mps2-an500` in the layout of `tests/TestSupport/M7/Qemu.lean`.  With `OVRDIS` set,
a byte that arrives while `USART_RDR` holds another replaces it and reception continues, so the
next `0x00` restores the framing's alignment after an overrun; with `OVRDIS` clear, an overrun
stops reception until software writes `ORECF`, which a step confined to `USART_ISR`,
`USART_RDR`, and `USART_TDR` cannot do.  `m7-windows delim-board` writes the first to
`delim.bin`, which `st-flash` writes to the board's flash at `0x08000000`, and `m7-windows
delim-qemu` writes the second to `delim-cmsdk-qemu.bin`.
-/

namespace TestSupport.M7.Delim

open LeanExe.M7

/-- The words of the initial state. -/
abbrev dlState : List UInt64 := dlWords dlInit

/-- The board's image from the self-loop on, with the initialization `initOvrdis`. -/
def boardProgram : GenM (List Instr) :=
  Nucleo.programWith Nucleo.initOvrdis dlCompiled.module 22 dlState

/-- The bytes of the board's image. -/
def boardImage : GenM (List UInt8) :=
  Nucleo.imageWith Nucleo.initOvrdis dlCompiled.module 22 dlState

/-- The address of the loop's head of `main` in the board's image. -/
def boardHead : UInt32 := Nucleo.loopHeadWith Nucleo.initOvrdis dlState

/-- QEMU's image from the self-loop on. -/
def qemuProgram : GenM (List Instr) :=
  bootProgram Qemu.boot dlCompiled.module 23 dlState Qemu.stackLimit Qemu.devBase

/-- The bytes of QEMU's image. -/
def qemuImage : GenM (List UInt8) := do
  return bootBytes Qemu.boot (← qemuProgram)

/-- The address of the loop's head of `main` in QEMU's image. -/
def qemuHead : UInt32 := after Qemu.boot.base (mainStart dlState)

end TestSupport.M7.Delim
