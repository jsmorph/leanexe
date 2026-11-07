import LeanExe.M7.Board
import TestSupport.M7.Qemu
import Demos.Energy.Loop

/-!
The images of the energy controller's gateway through the Cortex-M7 back end, both from the state
`gwInit`: the program of `gwTickUsart3`, function 34 of `gwCompiled.module`, for the NUCLEO-F767ZI
in the layout of `LeanExe/M7/Board.lean`, and the program of `gwTick`, function 33, for QEMU's
`mps2-an500` in the layout of `tests/TestSupport/M7/Qemu.lean`.  `m7-windows gateway-board`
writes the first to `gateway.bin`, which `st-flash` writes to the board's flash at `0x08000000`,
and `m7-windows gateway-qemu` writes the second.

`gwSizes` lists the sizes in units of the functions that calls reach from either step, in the
order of `reachFrom`, which the kernel's checks of the gateway's images in parts take.  A
function's size depends on its body and on the signatures of its callees, and not on any address.
The two steps differ only in the constants of the UART's registers and bits, whose words all lie
below 2^16 and so take one `MOVW` each, and the list is the same for both steps.
-/

namespace TestSupport.M7.Gw

open LeanExe.M7 Demos.Energy

/-- The words of the gateway's initial state. -/
abbrev gwState : List UInt64 := gwWords gwInit

/-- The board's image from the self-loop on. -/
def boardProgram : GenM (List Instr) := LeanExe.M7.Nucleo.program gwCompiled.module 34 gwState

/-- The bytes of the board's image. -/
def boardImage : GenM (List UInt8) := LeanExe.M7.Nucleo.image gwCompiled.module 34 gwState

/-- The address of the loop's head of `main` in the board's image. -/
def boardHead : UInt32 := LeanExe.M7.Nucleo.loopHead gwState

/-- QEMU's image from the self-loop on. -/
def qemuProgram : GenM (List Instr) :=
  bootProgram Qemu.boot gwCompiled.module 33 gwState Qemu.stackLimit Qemu.devBase

/-- The bytes of QEMU's image. -/
def qemuImage : GenM (List UInt8) := do
  return bootBytes Qemu.boot (← qemuProgram)

/-- The address of the loop's head of `main` in QEMU's image. -/
def qemuHead : UInt32 := after Qemu.boot.base (mainStart gwState)

/-- The sizes in units of the functions that calls reach from `gwTickUsart3` and from `gwTick`. -/
def gwSizes : List Nat :=
  [795, 9735, 31, 110, 154, 596, 134, 5550, 96, 512, 186, 230, 118, 177, 114, 2853, 469, 390, 390,
    146, 547, 141, 84, 69, 174, 69, 174, 42, 81, 81, 160, 43]

end TestSupport.M7.Gw
