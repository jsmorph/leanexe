import TestSupport.M7.DelimLoop

/-!
The kernel's check of the image of the echo of records of `dlUsart3Tick` for the NUCLEO-F767ZI
that `m7-windows delim-board` writes, `delim.bin`, and the theorems over that file.
`tests/baremetal/m7-board.sh check delim` elaborates this file in the directory of the image, so
that `file_nat%` and `file_size%` read it, and no build target includes it.  The kernel evaluates
`bootProgram` on `dlUsart3Tick`'s module and index and the words of the initial state `dlInit`,
with the layout `bootWith initOvrdis`, whose initialization writes `OVRDIS` to `USART_CR3` before
the write of `USART_CR1` that sets UE, and checks that the file's bytes are those of the vector
table and the instructions.

`dl_board` states the loop theorem for every code map that holds the file's bytes in flash at
both of its addresses, `dl_board_runs` that the run never stops, `dl_board_steps` that each
window takes at most 151,558 steps of the model, and `dl_board_prefix` that the bytes that the
run writes to `USART_TDR` begin the encoded answers of `echoMach` to the nonempty segments of the
bytes that it reads from `USART_RDR`, all of them whenever a window reads a byte.  The theorems
hold of the processor under the run conditions of `LeanExe/M7/Proof/Board.lean`: a power-on
reset, or an NRST reset with the debug registers at their power-on values, with BOOT0 low and
BOOT_ADD0 0x0080, software watchdogs (OPTCR 0xFFFFAAFD), and no interrupt, NMI, debug halt,
debugger access, or DMA during the run.
-/

namespace TestSupport.M7.DelimBoardFile

open LeanExe.M7 LeanExe.M7.Nucleo LeanExe.Requests TestSupport.M7.Delim

def dlBytes : Nat := file_nat% "delim.bin"
def dlSize : Nat := file_size% "delim.bin"

/-- The file holds the bytes of the echo of records' image. -/
theorem dl_file : bootFileOk (bootWith initOvrdis) boardProgram dlBytes dlSize = true := by
  decide +kernel

/-- The echo of records on the NUCLEO-F767ZI from reset, over the image file: for every sequence
`σ` of the values that device reads return, every number `N` of windows, every code map that holds
the file's bytes in flash from `0x08000000` and from `0x00200000`, and every state that reset
gives from the vector table at `0x00200000`, the model reaches the loop's head of `main` with the
accesses of `initOvrdis` followed by those of the first `N` windows of `dlUsart3Tick` from
`dlInit`, whose reads take the values of `σ` after the initialization's 11. -/
theorem dl_board (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code dlBytes dlSize) (b : State) (hb : Reset code flashItcm b) :
    ∃ s, Reach platform σ code b s ∧ s.pc = boardHead ∧
      s.trace = initTrace initOvrdis σ ++
        windows (reqTrace (devBus devBase) dlUsart3Tick dlInit
          (fun k => σ (k + initReads initOvrdis))) N :=
  board_loop dl_file hf b hb N

/-- The echo of records' windows from reset over the image file, counted: the run reaches the
loop's head after the initialization's `c` steps, and window `i` takes `cs[i]` steps, at most
151,558, after which the run is at the head with the accesses of the initialization and of the
first `i + 1` windows. -/
theorem dl_board_steps (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code dlBytes dlSize) (b : State) (hb : Reset code flashItcm b) :
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 151558) ∧
      ∀ i ≤ N, ∃ s, run platform σ code (c + (cs.take i).sum) b = some s ∧ s.pc = boardHead ∧
        s.trace = initTrace initOvrdis σ ++
          windows (reqTrace (devBus devBase) dlUsart3Tick dlInit
            (fun k => σ (k + initReads initOvrdis))) i :=
  board_loop_steps dl_file hf b hb N

/-- The echo of records' run from reset over the image file succeeds for every number of steps. -/
theorem dl_board_runs (σ : Nat → UInt32) (code : UInt32 → Option UInt16)
    (hf : Flash code dlBytes dlSize) (b : State) (hb : Reset code flashItcm b) :
    ∀ k, ∃ t, run platform σ code k b = some t :=
  board_loop_runs dl_file hf b hb

/-- The echo of records' answers on the NUCLEO-F767ZI from reset, over the image file: for every
sequence `σ` of the values that device reads return and every number `N` of windows, the run
reaches the initialization's accesses followed by the accesses `w` of the first `N` windows, the
bytes that `w` writes to `USART_TDR` begin the encoded answers of `echoMach` to the nonempty
segments of the bytes that `w` reads from `USART_RDR`, each followed by `0x00`, and they are all
those answers when window `N` reads a byte. -/
theorem dl_board_prefix (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code dlBytes dlSize) (b : State) (hb : Reset code flashItcm b) :
    let σ' := fun k => σ (k + initReads initOvrdis)
    let w := windows (reqTrace (devBus devBase) dlUsart3Tick dlInit σ') N
    ∃ s, Reach platform σ code b s ∧ s.trace = initTrace initOvrdis σ ++ w ∧
      dataOut (devBus devBase) dlUsart3 w <+:
        (delimAnswers echoMach 36 0 ((dataIn (devBus devBase) dlUsart3 w).map
          UInt64.toUInt8)).map UInt8.toUInt64 ∧
      (dataIn (devBus devBase) dlUsart3 (reqTrace (devBus devBase) dlUsart3Tick dlInit σ' N) ≠
          [] →
        dataOut (devBus devBase) dlUsart3 w =
          (delimAnswers echoMach 36 0 ((dataIn (devBus devBase) dlUsart3 w).map
            UInt64.toUInt8)).map UInt8.toUInt64) :=
  board_prefix dl_file hf b hb N

end TestSupport.M7.DelimBoardFile

#print axioms TestSupport.M7.DelimBoardFile.dl_board
#print axioms TestSupport.M7.DelimBoardFile.dl_board_runs
#print axioms TestSupport.M7.DelimBoardFile.dl_board_steps
#print axioms TestSupport.M7.DelimBoardFile.dl_board_prefix
#print axioms TestSupport.M7.DelimBoardFile.dl_file
#print axioms TestSupport.M7.Delim.board_loop
#print axioms TestSupport.M7.Delim.board_loop_steps
#print axioms TestSupport.M7.Delim.board_loop_runs
#print axioms TestSupport.M7.Delim.board_prefix
#print axioms TestSupport.M7.Delim.dl_requests
#print axioms TestSupport.M7.Delim.dl_confined
#print axioms TestSupport.M7.Delim.dlPhases_abs
#print axioms TestSupport.M7.dl_static
#print axioms LeanExe.Requests.delim_prefix
#print axioms LeanExe.Requests.delim_answered
#print axioms LeanExe.Requests.cobsDecode_eq_some_iff
