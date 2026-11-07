import TestSupport.M7.GwLoop
import LeanExe.M7.Proof.Parts

/-!
The kernel's check of the image of the gateway of `gwTickUsart3` for the NUCLEO-F767ZI that
`m7-windows gateway-board` writes, `gateway.bin`, in parts, and the theorems over that file.
`tests/baremetal/m7-board.sh check gateway` elaborates this file in the directory of the image, so
that `file_nat%` and `file_size%` read it, and no build target includes it.  The check of the
whole image as one declaration does not fit 16 GiB, so each part has a declaration of its own:
the vector table, the self-loop, and the board's initialization, then `main`, the step
`gwTickUsart3`, `gwTickWith`, two groups of the other functions that calls reach from the step,
each checking its entry of `gwSizes`, and the trap stubs with `udivmod64`.  `bootFileOk_parts`
joins them into the check `bootFileOk` that the board's theorems take.

`gw_board` states the loop theorem for every code map that holds the file's bytes in flash at
both of its addresses, `gw_board_runs` that the run never stops, and `gw_board_prefix` that the
bytes that the run writes to `USART_TDR` begin the bytes of the gateway's output records for the
input records that the bytes it reads from `USART_RDR` encode.  The theorems hold of the processor
under the run conditions of `LeanExe/M7/Proof/Board.lean`: a power-on reset with BOOT0 low and
BOOT_ADD0 0x0080, software watchdogs (OPTCR 0xFFFFAAFD), and no interrupt, NMI, debug halt,
debugger access, or DMA during the run.
-/

namespace TestSupport.M7.GwBoardFile

open LeanExe.M7 hiding decode
open LeanExe.M7.Nucleo LeanExe.Requests TestSupport.M7.Gw Demos.Energy

def gwBytes : Nat := file_nat% "gateway.bin"
def gwSize : Nat := file_size% "gateway.bin"

/-- The vector table, the self-loop, and the board's initialization. -/
theorem gw_head : bootHeadOk boot gwBytes = true := by
  decide +kernel

theorem gw_main :
    mainPartOk gwCompiled.module 34 gwState boot.base devBase gwBytes (bootHead boot).length =
      true := by
  decide +kernel

/-- `gwTickUsart3`. -/
theorem gw_fns0 : functionsPartOk gwCompiled.module 34 gwState boot.base stackLimit gwSizes gwBytes
    (bootHead boot).length 0 1 = true := by
  decide +kernel

/-- `gwTickWith`, the largest function. -/
theorem gw_fns1 : functionsPartOk gwCompiled.module 34 gwState boot.base stackLimit gwSizes gwBytes
    (bootHead boot).length 1 2 = true := by
  decide +kernel

/-- `readReq`, `writeReq`, `shiftIn`, `gateway`, `siteProf`, and `gatewayWith`. -/
theorem gw_fns2 : functionsPartOk gwCompiled.module 34 gwState boot.base stackLimit gwSizes gwBytes
    (bootHead boot).length 2 8 = true := by
  decide +kernel

/-- The other functions. -/
theorem gw_fns8 : functionsPartOk gwCompiled.module 34 gwState boot.base stackLimit gwSizes gwBytes
    (bootHead boot).length 8 32 = true := by
  decide +kernel

theorem gw_tail :
    tailPartOk gwState gwSizes udivmod64 gwBytes (bootHead boot).length 242 = true := by
  decide +kernel

theorem gw_size :
    gwSize = (bootHead boot).length + (4 * (mainSize gwState + gwSizes.sum) + 242) ∧
      gwBytes < 256 ^ gwSize := by
  decide +kernel

/-- The file holds the bytes of the gateway's image. -/
theorem gw_file : bootFileOk boot boardProgram gwBytes gwSize = true :=
  bootFileOk_parts gw_head gw_main gw_count.1
    (functionsPartOk_append
      (functionsPartOk_append (functionsPartOk_append gw_fns0 gw_fns1) gw_fns2) gw_fns8)
    gw_tail gw_size.1 gw_size.2

/-- The gateway on the NUCLEO-F767ZI from reset, over the image file: for every sequence `σ` of
the values that device reads return, every number `N` of windows, every code map that holds the
file's bytes in flash from `0x08000000` and from `0x00200000`, and every state that reset gives
from the vector table at `0x00200000`, the model reaches the loop's head of `main` with the
initialization's accesses followed by those of the first `N` windows of `gwTickUsart3` from the
state `gwInit`, whose reads take the values of `σ` after the initialization's 11. -/
theorem gw_board (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code gwBytes gwSize) (b : State) (hb : Reset code flashItcm b) :
    ∃ s, Reach platform σ code b s ∧ s.pc = boardHead ∧
      s.trace = initTrace init σ ++
        windows (reqTrace (devBus devBase) gwTickUsart3 gwInit
          (fun k => σ (k + initReads init))) N :=
  board_loop gw_file hf b hb N

/-- The gateway's run from reset over the image file succeeds for every number of steps. -/
theorem gw_board_runs (σ : Nat → UInt32) (code : UInt32 → Option UInt16)
    (hf : Flash code gwBytes gwSize) (b : State) (hb : Reset code flashItcm b) :
    ∀ k, ∃ t, run platform σ code k b = some t :=
  board_loop_runs gw_file hf b hb

/-- The gateway's records on the NUCLEO-F767ZI from reset, over the image file: for every sequence
`σ` of the values that device reads return and every number `N` of windows, the run reaches the
initialization's accesses followed by the accesses `w` of the first `N` windows, and the bytes that
`w` writes to `USART_TDR` begin the bytes of the gateway's output records for the input records of
18 words that the bytes that `w` reads from `USART_RDR` encode. -/
theorem gw_board_prefix (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code gwBytes gwSize) (b : State) (hb : Reset code flashItcm b) :
    let w := windows (reqTrace (devBus devBase) gwTickUsart3 gwInit
      (fun k => σ (k + initReads init))) N
    ∃ s, Reach platform σ code b s ∧ s.trace = initTrace init σ ++ w ∧
      dataOut (devBus devBase) gwUsart3 w <+:
        outBytes gwSpec gw0 (decode 18 (dataIn (devBus devBase) gwUsart3 w)).recs :=
  board_prefix gw_file hf b hb N

end TestSupport.M7.GwBoardFile

#print axioms TestSupport.M7.GwBoardFile.gw_board
#print axioms TestSupport.M7.GwBoardFile.gw_board_runs
#print axioms TestSupport.M7.GwBoardFile.gw_board_prefix
#print axioms TestSupport.M7.GwBoardFile.gw_file
#print axioms TestSupport.M7.Gw.board_loop
#print axioms TestSupport.M7.Gw.board_loop_runs
#print axioms TestSupport.M7.Gw.board_prefix
#print axioms TestSupport.M7.Gw.windows_prefix
#print axioms TestSupport.M7.Gw.gw_requests
#print axioms TestSupport.M7.Gw.gw_confined
#print axioms TestSupport.M7.Gw.gw_count
#print axioms LeanExe.M7.Nucleo.windows_confined
#print axioms LeanExe.M7.bootFileOk_parts
