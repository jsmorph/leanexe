import TestSupport.M7.NucleoLoop

/-!
The kernel's check of the image of the echo of `usart3Tick` for the NUCLEO-F767ZI that
`m7-windows board` writes, `echo.bin`, and the theorems over that file.  `tests/baremetal/m7-board.sh`
elaborates this file in the directory of the image, so that `file_nat%` and `file_size%` read it,
and no build target includes it.  The kernel evaluates `bootProgram` on `usart3Tick`'s module and
index and the initial state 3, with the board's layout and initialization, and checks that the
file's bytes are those of the vector table and the instructions.

`echo_board` states the loop theorem for every code map that holds the file's bytes in flash at
both of its addresses, and `echo_board_runs` that the run never stops.  Both hold of the
processor under the run conditions of `LeanExe/M7/Proof/Board.lean`: a power-on reset with BOOT0
low and BOOT_ADD0 0x0080, software watchdogs (OPTCR 0xFFFFAAFD), and no interrupt, NMI, debug halt,
debugger access, or DMA during the run.
-/

namespace TestSupport.M7.NucleoFile

open LeanExe.M7 LeanExe.M7.Nucleo LeanExe.Requests TestSupport.M7.Nucleo TestSupport.Bare

def echoBytes : Nat := file_nat% "echo.bin"
def echoSize : Nat := file_size% "echo.bin"

/-- The file holds the bytes of the echo's image. -/
theorem echo_file : bootFileOk boot echoProgram echoBytes echoSize = true := by
  decide +kernel

/-- The echo on the NUCLEO-F767ZI from reset, over the image file: for every sequence `σ` of the
values that device reads return, every number `N` of windows, every code map that holds the
file's bytes in flash from `0x08000000` and from `0x00200000`, and every state that reset gives
from the vector table at `0x00200000`, the model reaches the loop's head of `main` with the
initialization's accesses followed by those of the first `N` windows of `usart3Tick` from the
state 3, whose reads take the values of `σ` after the initialization's 11. -/
theorem echo_board (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code echoBytes echoSize) (b : State) (hb : Reset code flashItcm b) :
    ∃ s, Reach platform σ code b s ∧ s.pc = echoHead ∧
      s.trace = initTrace init σ ++
        windows (reqTrace (devBus devBase) usart3Tick 3 (fun k => σ (k + initReads init))) N :=
  echo_loop echo_file hf b hb N

/-- The echo's run from reset over the image file succeeds for every number of steps. -/
theorem echo_board_runs (σ : Nat → UInt32) (code : UInt32 → Option UInt16)
    (hf : Flash code echoBytes echoSize) (b : State) (hb : Reset code flashItcm b) :
    ∀ k, ∃ t, run platform σ code k b = some t :=
  echo_runs echo_file hf b hb

end TestSupport.M7.NucleoFile

#print axioms TestSupport.M7.NucleoFile.echo_board
#print axioms TestSupport.M7.NucleoFile.echo_board_runs
#print axioms TestSupport.M7.NucleoFile.echo_file
#print axioms TestSupport.M7.Nucleo.echo_loop
#print axioms TestSupport.M7.Nucleo.echo_runs
#print axioms TestSupport.M7.Nucleo.echo_confined
#print axioms TestSupport.M7.Nucleo.usart3_requests
#print axioms LeanExe.M7.Nucleo.board_run
#print axioms LeanExe.M7.Nucleo.board_runs
#print axioms LeanExe.M7.Nucleo.init_addrs
#print axioms LeanExe.M7.init_runs
#print axioms LeanExe.M7.runs_forever
