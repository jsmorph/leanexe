import TestSupport.M7.Area
import LeanExe.M7.Proof.Board

/-!
The kernel's check of the image of `tests/TestSupport/M7/Area.lean` that `m7-windows area-board`
writes, `area.bin`, and the setup's theorem over that file.  `tests/baremetal/m7-board.sh check
area` elaborates this file in the directory of the image, so that `file_nat%` and `file_size%` read
it, and no build target includes it.  The kernel evaluates `bootProgram` on the layout `areaBoot`
of the CRC-32 step's module, whose setup holds the nonzero words of the area's prefix as
immediates, and on the echo's module, index, and initial state, and checks that the file's bytes
are those of the vector table and the instructions.

`area_setup` states, for every code map that holds the file's bytes in flash at both of its
addresses and every state that reset gives from the vector table at `0x00200000`, that the model
reaches the board's initialization with SP at the top of DTCM, an empty trace, and the store in
which the CRC-32 step's module starts held in the area at DTCM's base, below the stack's limit at
the area's end.  It holds of the processor under the run conditions of
`LeanExe/M7/Proof/Board.lean`.
-/

namespace TestSupport.M7.AreaFile

open Wasm LeanExe.M7 LeanExe.M7.Nucleo TestSupport.M7.Area TestSupport.M7.Crc

def areaFileBytes : Nat := file_nat% "area.bin"
def areaFileSize : Nat := file_size% "area.bin"

/-- The file holds the bytes of the image. -/
theorem area_file :
    bootFileOk (areaBoot crcStepCompiled.module) areaEcho areaFileBytes areaFileSize = true := by
  decide +kernel

/-- The module's globals are four `i64`s. -/
theorem crcStep_globals :
    LeanExe.globalTypesOf crcStepCompiled.module = some [.i64, .i64, .i64, .i64] := by
  decide +kernel

/-- The setup over the image file, from reset to the board's initialization. -/
theorem area_setup (σ : Nat → UInt32) (code : UInt32 → Option UInt16)
    (hf : Flash code areaFileBytes areaFileSize) (b : State) (hb : Reset code flashItcm b) :
    ∃ t, Reach platform σ code b t ∧ t.pc = areaInit ∧ CodeAt code t.pc (initCode init) ∧
      t.sp = stackTop ∧ t.lr = 0xFFFFFFFF ∧ t.trace = [] ∧ t.reads = 0 ∧
      StoreRel platform areaHeader areaEnd areaPages [.i64, .i64, .i64, .i64]
        (LeanExe.initStore crcStepCompiled.module areaPages) t :=
  board_setup (by decide +kernel) crcStep_globals area_file hf b hb

end TestSupport.M7.AreaFile

#print axioms TestSupport.M7.AreaFile.area_file
#print axioms TestSupport.M7.AreaFile.crcStep_globals
#print axioms TestSupport.M7.AreaFile.area_setup
#print axioms LeanExe.M7.Nucleo.board_setup
#print axioms LeanExe.M7.setup_boot
#print axioms LeanExe.M7.setup_run
#print axioms LeanExe.M7.run_clearLoop
#print axioms LeanExe.M7.run_storeWords
#print axioms LeanExe.M7.storeRel_init
