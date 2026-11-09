import LeanExe.M7.Board
import TestSupport.M7.Qemu
import TestSupport.M7.Delim

/-!
The images of the echo of records of `tests/TestSupport/M7/Delim.lean`, from the state `dlInit`:
the program of `dlCmsdkTick`, function 23 of `dlCompiled.module`, for QEMU's `mps2-an500` in the
layout of `tests/TestSupport/M7/Qemu.lean`.  `m7-windows delim-qemu` writes it to
`delim-cmsdk-qemu.bin`.
-/

namespace TestSupport.M7.Delim

open LeanExe.M7

/-- The words of the initial state. -/
abbrev dlState : List UInt64 := dlWords dlInit

/-- QEMU's image from the self-loop on. -/
def qemuProgram : GenM (List Instr) :=
  bootProgram Qemu.boot dlCompiled.module 23 dlState Qemu.stackLimit Qemu.devBase

/-- The bytes of QEMU's image. -/
def qemuImage : GenM (List UInt8) := do
  return bootBytes Qemu.boot (← qemuProgram)

/-- The address of the loop's head of `main` in QEMU's image. -/
def qemuHead : UInt32 := after Qemu.boot.base (mainStart dlState)

end TestSupport.M7.Delim
