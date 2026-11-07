import LeanExe.M7.Board
import LeanExe.M7.Setup
import TestSupport.M7.Qemu
import TestSupport.M7.Sha

/-!
The images of the SHA-256 step through the Cortex-M7 back end, both from the state `shaInit`, which
no theorem covers: the program of `shaUsart3Tick`, function 13 of `shaStepCompiled.module`, for
the NUCLEO-F767ZI in the layout of `LeanExe/M7/Board.lean`, and the program of `shaCmsdkTick`,
function 13 of `shaCmsdkCompiled.module`, for QEMU's `mps2-an500` in the layout of
`tests/TestSupport/M7/Qemu.lean`.  Each image runs the setup of the generator's area of
`LeanExe/M7/Setup.lean` before its initialization, which clears the area and writes the nonzero
words of its first bytes, among them the round constants at the memory's byte 4096, and the
stack's limit lies at the area's end.  `m7-windows sha-board` writes the first to `sha.bin`,
which `st-flash` writes to the board's flash at `0x08000000`, and `m7-windows sha-qemu` writes
the second.
-/

namespace TestSupport.M7.ShaImages

open LeanExe.M7 TestSupport.M7.Sha

/-- The words of the step's initial state. -/
abbrev shaState : List UInt64 := shaWords shaInit

/-- The board's layout: `areaBoot` of `LeanExe/M7/Board.lean`, the board's vector table and SP,
and the setup of the area before the board's initialization. -/
def boardBoot : Boot := Nucleo.areaBoot shaStepCompiled.module

/-- The board's image from the self-loop on. -/
def boardProgram : GenM (List Instr) :=
  bootProgram boardBoot shaStepCompiled.module 13 shaState areaEnd Nucleo.devBase

/-- The bytes of the board's image. -/
def boardImage : GenM (List UInt8) := do
  return bootBytes boardBoot (← boardProgram)

/-- The address of the loop's head of `main` in the board's image. -/
def boardHead : UInt32 := after boardBoot.base (mainStart shaState)

/-- QEMU's layout: QEMU's vector table and SP, and the setup of the area before UART0's
initialization. -/
def qemuBoot : Boot :=
  Qemu.boot.setup (setupCode areaHeader areaPages shaCmsdkCompiled.module)

/-- QEMU's image from the self-loop on. -/
def qemuProgram : GenM (List Instr) :=
  bootProgram qemuBoot shaCmsdkCompiled.module 13 shaState areaEnd Qemu.devBase

/-- The bytes of QEMU's image. -/
def qemuImage : GenM (List UInt8) := do
  return bootBytes qemuBoot (← qemuProgram)

/-- The address of the loop's head of `main` in QEMU's image. -/
def qemuHead : UInt32 := after qemuBoot.base (mainStart shaState)

end TestSupport.M7.ShaImages
