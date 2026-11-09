import TestSupport.M7.BmsLoop

/-!
The kernel's check of the image of the BMS step `bmsTickUsart3` for the NUCLEO-F767ZI that
`m7-windows bms-board` writes, `bms.bin`, and the board theorems B1, B2, B3, B3a, and B5 of
`Demos/Bms/requirements.md` over that file.  `tests/baremetal/m7-board.sh check bms` elaborates this
file in the directory of the image, so that `file_nat%` and `file_size%` read it, and no build
target includes it.  The kernel evaluates `bootProgram` on `bmsTickUsart3`'s module and index and
the words of the initial state `bmsInit`, with the layout `bootWith initOvrdis`, whose
initialization writes `OVRDIS` to `USART_CR3` before the write of `USART_CR1` that sets UE, and
checks that the file's bytes are those of the vector table and the instructions.

For every state that reset gives while the flash holds the file's bytes at both of its addresses,
every sequence `σ` of the values that reads return, and every number `N` of windows, B1 is
`bms_board`, the trace of the initialization and of the first `N` windows, `bms_board_runs`, the
run that never stops, and `bms_board_prefix`, the bytes written to `USART_TDR` as a prefix of the
encoded answers `answerAt (inputs bs) t` of the machine's run over the non-empty segments of the
bytes `bs` read from `USART_RDR`.  B2 is `bms_confined`, B3 `bms_board_steps`, each window in at
most 202,799 steps of the model, B3a `bms_board_poll`, each window other than the window of a
delimiter after a non-empty segment in at most 3,301, and B5 `bms_board_safe`: every complete
answer among the bytes written whose permit byte is not 0 is the answer `a_n` of that run, and
`Permitted`, the
conclusion of M1, holds of it.  The theorems hold of the processor under the run conditions of
`LeanExe/M7/Proof/Board.lean`: a power-on reset, or an NRST reset with the debug registers at their
power-on values, with BOOT0 low and BOOT_ADD0 0x0080, software watchdogs (OPTCR 0xFFFFAAFD), and no
interrupt, NMI, debug halt, debugger access, or DMA during the run.
-/

namespace TestSupport.M7.BmsBoardFile

open LeanExe.M7 LeanExe.M7.Nucleo LeanExe.Requests TestSupport.M7.Bms Demos.Bms.Program
open Demos.Bms.Spec (records inputs answerAt encodeAnswer field Permitted)

def bmsBytes : Nat := file_nat% "bms.bin"
def bmsSize : Nat := file_size% "bms.bin"

/-- The file holds the bytes of the BMS step's image. -/
theorem bms_file : bootFileOk (bootWith initOvrdis) boardProgram bmsBytes bmsSize = true := by
  decide +kernel

/-- B1: the BMS step on the NUCLEO-F767ZI from reset, over the image file: for every sequence `σ`
of the values that device reads return, every number `N` of windows, every code map that holds the
file's bytes in flash from `0x08000000` and from `0x00200000`, and every state that reset gives
from the vector table at `0x00200000`, the model reaches the loop's head of `main` with the
accesses of `initOvrdis` followed by those of the first `N` windows of `bmsTickUsart3` from
`bmsInit`, whose reads take the values of `σ` after the initialization's 11. -/
theorem bms_board (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code bmsBytes bmsSize) (b : State) (hb : Reset code flashItcm b) :
    ∃ s, Reach platform σ code b s ∧ s.pc = boardHead ∧
      s.trace = initTrace initOvrdis σ ++
        windows (reqTrace (devBus devBase) bmsTickUsart3 bmsInit
          (fun k => σ (k + initReads initOvrdis))) N :=
  board_loop bms_file hf b hb N

/-- B3: the windows from reset over the image file, counted: the run reaches the loop's head after
the initialization's `c` steps, and window `i` takes `cs[i]` steps, at most 202,799, after which
the run is at the head with the accesses of the initialization and of the first `i + 1`
windows. -/
theorem bms_board_steps (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code bmsBytes bmsSize) (b : State) (hb : Reset code flashItcm b) :
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 202799) ∧
      ∀ i ≤ N, ∃ s, run platform σ code (c + (cs.take i).sum) b = some s ∧ s.pc = boardHead ∧
        s.trace = initTrace initOvrdis σ ++
          windows (reqTrace (devBus devBase) bmsTickUsart3 bmsInit
            (fun k => σ (k + initReads initOvrdis))) i :=
  board_loop_steps bms_file hf b hb N

/-- B3a: the windows from reset over the image file, counted, with the windows other than the
window of a delimiter bounded apart: window `i` takes `cs[i]` steps, at most 202,799, and at most
3,301, 16 of `main` and the dispatch with the call of `bmsPoll`, when its state and the value that
it receives do not satisfy `BmsDecodes`, which holds of the window of a `0x00` after a non-empty
segment alone. -/
theorem bms_board_poll (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code bmsBytes bmsSize) (b : State) (hb : Reset code flashItcm b) :
    let σ' := fun k => σ (k + initReads initOvrdis)
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 202799) ∧
      (∀ i x, cs[i]? = some x →
        ¬ BmsDecodes (reqRun bmsTickUsart3 bmsInit σ' i).state
          (reqRun bmsTickUsart3 bmsInit σ' i).last → x ≤ 3301) ∧
      ∀ i ≤ N, ∃ s, run platform σ code (c + (cs.take i).sum) b = some s ∧ s.pc = boardHead ∧
        s.trace = initTrace initOvrdis σ ++
          windows (reqTrace (devBus devBase) bmsTickUsart3 bmsInit σ') i :=
  board_loop_poll bms_file hf b hb N

/-- B1: the run from reset over the image file succeeds for every number of steps. -/
theorem bms_board_runs (σ : Nat → UInt32) (code : UInt32 → Option UInt16)
    (hf : Flash code bmsBytes bmsSize) (b : State) (hb : Reset code flashItcm b) :
    ∀ k, ∃ t, run platform σ code k b = some t :=
  board_loop_runs bms_file hf b hb

/-- B1: the answers on the NUCLEO-F767ZI from reset, over the image file: for every sequence `σ`
of the values that device reads return and every number `N` of windows, the run reaches the
initialization's accesses followed by the accesses `w` of the first `N` windows, and the bytes
that `w` writes to `USART_TDR` begin the encoded answers `answerAt (inputs bs) t` of the
specification's machine to the non-empty segments `t` of the bytes `bs` that `w` reads from
`USART_RDR`, each followed by `0x00`. -/
theorem bms_board_prefix (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code bmsBytes bmsSize) (b : State) (hb : Reset code flashItcm b) :
    let σ' := fun k => σ (k + initReads initOvrdis)
    let w := windows (reqTrace (devBus devBase) bmsTickUsart3 bmsInit σ') N
    let bs := (dataIn (devBus devBase) bmsUsart3 w).map UInt64.toUInt8
    ∃ s, Reach platform σ code b s ∧ s.trace = initTrace initOvrdis σ ++ w ∧
      dataOut (devBus devBase) bmsUsart3 w <+:
        ((List.range (records bs).length).flatMap fun t =>
          cobsEncode (encodeAnswer (answerAt (inputs bs) t)) ++ [0]).map UInt8.toUInt64 :=
  board_prefix_stream bms_file hf b hb N

/-- B5: for every sequence `σ` of the values that device reads return and every number `N` of
windows, every complete segment of the bytes written to `USART_TDR` that decodes to an answer
whose permit byte is not 0 is the encoded answer `a_m` of the specification's machine's run over
the non-empty segments of the bytes `bs` read from `USART_RDR`, and M1's conclusion
`Permitted (inputs bs) m i j` holds of it for its last reset acceptance `i` and last start `j`. -/
theorem bms_board_safe (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code bmsBytes bmsSize) (b : State) (hb : Reset code flashItcm b) :
    let σ' := fun k => σ (k + initReads initOvrdis)
    let w := windows (reqTrace (devBus devBase) bmsTickUsart3 bmsInit σ') N
    let bs := (dataIn (devBus devBase) bmsUsart3 w).map UInt64.toUInt8
    let out := (dataOut (devBus devBase) bmsUsart3 w).map UInt64.toUInt8
    ∃ s, Reach platform σ code b s ∧ s.trace = initTrace initOvrdis σ ++ w ∧
      ∀ (m : Nat) (seg raw : List UInt8), (segments out)[m]? = some seg →
        cobsDecode seg = some raw → field raw 9 1 ≠ 0 →
          m < (records bs).length ∧ raw = encodeAnswer (answerAt (inputs bs) m) ∧
            ∃ i j, Permitted (inputs bs) m i j :=
  board_safe bms_file hf b hb N

end TestSupport.M7.BmsBoardFile

#print axioms TestSupport.M7.BmsBoardFile.bms_file
#print axioms TestSupport.M7.BmsBoardFile.bms_board
#print axioms TestSupport.M7.BmsBoardFile.bms_board_steps
#print axioms TestSupport.M7.BmsBoardFile.bms_board_poll
#print axioms TestSupport.M7.BmsBoardFile.bms_board_runs
#print axioms TestSupport.M7.BmsBoardFile.bms_board_prefix
#print axioms TestSupport.M7.BmsBoardFile.bms_board_safe
#print axioms TestSupport.M7.Bms.bms_confined
#print axioms TestSupport.M7.Bms.board_prefix
#print axioms TestSupport.M7.bms_static
#print axioms TestSupport.M7.bms_parts_static
#print axioms TestSupport.M7.bms_pollPath
#print axioms TestSupport.M7.bms_poll
#print axioms TestSupport.M7.Bms.board_loop_poll
#print axioms Demos.Bms.Program.bmsPhases_abs
#print axioms Demos.Bms.Spec.m1_stream
#print axioms LeanExe.Requests.delim_prefix
