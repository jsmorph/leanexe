import TestSupport.M7.CrcLoop

/-!
The kernel's check of the image of the CRC-32 step `crcUsart3Tick` for the NUCLEO-F767ZI that
`m7-windows crc-board` writes, `crc.bin`, and the theorems over that file.
`tests/baremetal/m7-board.sh check crc` elaborates this file in the directory of the image, so that
`file_nat%` and `file_size%` read it, and no build target includes it.  The kernel evaluates
`bootProgram` on the layout `areaBoot` of the step's module, whose setup holds the nonzero words
of the area's prefix as immediates, and on the module, the index 5, and the initial state
`crcInit`, and checks that the file's bytes are those of the vector table and the instructions.

`crc_board` states the loop theorem for every code map that holds the file's bytes in flash at
both of its addresses, `crc_board_runs` that the run never stops, and `crc_board_prefix` that the
bytes that the run writes to `USART_TDR` begin the low bytes of the CRC-32 of the nonempty
prefixes of the bytes that it reads from `USART_RDR`, with at most one byte without a reply.  The
theorems hold of the processor under the run conditions of `LeanExe/M7/Proof/Board.lean`: a
power-on reset with BOOT0 low and BOOT_ADD0 0x0080, software watchdogs (OPTCR 0xFFFFAAFD), and no
interrupt, NMI, debug halt, debugger access, or DMA during the run.
-/

namespace TestSupport.M7.CrcBoardFile

open LeanExe.M7 LeanExe.M7.Nucleo LeanExe.Requests TestSupport.M7.Crc TestSupport.M7.CrcImages

def crcBytes : Nat := file_nat% "crc.bin"
def crcSize : Nat := file_size% "crc.bin"

/-- The file holds the bytes of the CRC-32 step's image. -/
theorem crc_file : bootFileOk boardBoot boardProgram crcBytes crcSize = true := by
  decide +kernel

/-- The CRC-32 step on the NUCLEO-F767ZI from reset, over the image file: for every sequence `σ`
of the values that device reads return, every number `N` of windows, every code map that holds
the file's bytes in flash from `0x08000000` and from `0x00200000`, and every state that reset
gives from the vector table at `0x00200000`, the model reaches the loop's head of `main` with the
initialization's accesses followed by those of the first `N` windows of `crcUsart3Tick` from the
state `crcInit`, whose reads take the values of `σ` after the initialization's 11. -/
theorem crc_board (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code crcBytes crcSize) (b : State) (hb : Reset code flashItcm b) :
    ∃ s, Reach platform σ code b s ∧ s.pc = boardHead ∧
      s.trace = initTrace init σ ++
        windows (reqTrace (devBus devBase) crcUsart3Tick crcInit
          (fun k => σ (k + initReads init))) N :=
  crc_loop crc_file hf b hb N

/-- The CRC-32 step's run from reset over the image file succeeds for every number of steps. -/
theorem crc_board_runs (σ : Nat → UInt32) (code : UInt32 → Option UInt16)
    (hf : Flash code crcBytes crcSize) (b : State) (hb : Reset code flashItcm b) :
    ∀ k, ∃ t, run platform σ code k b = some t :=
  crc_loop_runs crc_file hf b hb

/-- The CRC-32 step's replies on the NUCLEO-F767ZI from reset, over the image file: for every
sequence `σ` of the values that device reads return and every number `N` of windows, the run
reaches the initialization's accesses followed by the accesses `w` of the first `N` windows, the
bytes that `w` writes to `USART_TDR` begin the low bytes of the CRC-32 of the nonempty prefixes of
the bytes that `w` reads from `USART_RDR`, and at most one byte read has no reply. -/
theorem crc_board_prefix (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code crcBytes crcSize) (b : State) (hb : Reset code flashItcm b) :
    let w := windows (reqTrace (devBus devBase) crcUsart3Tick crcInit
      (fun k => σ (k + initReads init))) N
    ∃ s, Reach platform σ code b s ∧ s.trace = initTrace init σ ++ w ∧
      dataOut (devBus devBase) crcUsart3 w <+: crcReplies (dataIn (devBus devBase) crcUsart3 w) ∧
      (dataIn (devBus devBase) crcUsart3 w).length ≤
        (dataOut (devBus devBase) crcUsart3 w).length + 1 :=
  crc_prefix crc_file hf b hb N

end TestSupport.M7.CrcBoardFile

#print axioms TestSupport.M7.CrcBoardFile.crc_board
#print axioms TestSupport.M7.CrcBoardFile.crc_board_runs
#print axioms TestSupport.M7.CrcBoardFile.crc_board_prefix
#print axioms TestSupport.M7.CrcBoardFile.crc_file
#print axioms TestSupport.M7.Crc.crc_loop
#print axioms TestSupport.M7.Crc.crc_loop_runs
#print axioms TestSupport.M7.Crc.crc_prefix
#print axioms TestSupport.M7.Crc.crc_replies
#print axioms TestSupport.M7.Crc.crc_requests
#print axioms TestSupport.M7.Crc.crc_confined
#print axioms TestSupport.M7.Crc.crc_initStore
#print axioms LeanExe.M7.Nucleo.areaBoard_run
#print axioms LeanExe.M7.Nucleo.areaBoard_runs
#print axioms LeanExe.M7.setupBoot_run
