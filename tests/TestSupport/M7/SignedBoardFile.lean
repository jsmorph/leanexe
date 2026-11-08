import TestSupport.M7.SignedLoop

/-!
The kernel's check of the image of the signed step of `sgUsart3Tick` for the NUCLEO-F767ZI that
`m7-windows signed-board` writes, `signed.bin`, and the theorems over that file.
`tests/baremetal/m7-board.sh check signed` elaborates this file in the directory of the image, so
that `file_nat%` and `file_size%` read it, and no build target includes it.  The kernel evaluates
`bootProgram` on `sgUsart3Tick`'s module and index and the words of the initial state `sgInit`,
with the board's layout and initialization, and checks that the file's bytes are those of the
vector table and the instructions.

`sg_board` states the loop theorem for every code map that holds the file's bytes in flash at
both of its addresses, `sg_board_runs` that the run never stops, and `sg_board_steps` that each
window takes at most 1,404 steps of the model.  The three hold of the processor under the run
conditions of `LeanExe/M7/Proof/Board.lean`: a power-on reset, or an NRST reset with the debug
registers at their power-on values, with BOOT0 low and BOOT_ADD0 0x0080, software watchdogs
(OPTCR 0xFFFFAAFD), and no interrupt, NMI, debug halt, debugger access, or DMA during the run.
-/

namespace TestSupport.M7.SignedBoardFile

open LeanExe.M7 LeanExe.M7.Nucleo LeanExe.Requests TestSupport.M7.Signed

def sgBytes : Nat := file_nat% "signed.bin"
def sgSize : Nat := file_size% "signed.bin"

/-- The file holds the bytes of the signed step's image. -/
theorem sg_file : bootFileOk boot boardProgram sgBytes sgSize = true := by
  decide +kernel

/-- The signed step on the NUCLEO-F767ZI from reset, over the image file: for every sequence `σ`
of the values that device reads return, every number `N` of windows, every code map that holds
the file's bytes in flash from `0x08000000` and from `0x00200000`, and every state that reset
gives from the vector table at `0x00200000`, the model reaches the loop's head of `main` with the
initialization's accesses followed by those of the first `N` windows of `sgUsart3Tick` from
`sgInit`, whose reads take the values of `σ` after the initialization's 11. -/
theorem sg_board (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code sgBytes sgSize) (b : State) (hb : Reset code flashItcm b) :
    ∃ s, Reach platform σ code b s ∧ s.pc = boardHead ∧
      s.trace = initTrace init σ ++
        windows (reqTrace (devBus devBase) sgUsart3Tick sgInit (fun k => σ (k + initReads init)))
          N :=
  board_loop sg_file hf b hb N

/-- The signed step's windows from reset over the image file, counted: for every `σ`, `N`, code
map that holds the file's bytes in flash, and state that reset gives, the run reaches the loop's
head after the initialization's `c` steps, and window `i` takes `cs[i]` steps, at most 1,404,
after which the run is at the head with the accesses of the initialization and of the first
`i + 1` windows. -/
theorem sg_board_steps (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : Flash code sgBytes sgSize) (b : State) (hb : Reset code flashItcm b) :
    ∃ (c : Nat) (cs : List Nat), cs.length = N ∧ (∀ x ∈ cs, x ≤ 1404) ∧
      ∀ i ≤ N, ∃ s, run platform σ code (c + (cs.take i).sum) b = some s ∧ s.pc = boardHead ∧
        s.trace = initTrace init σ ++
          windows (reqTrace (devBus devBase) sgUsart3Tick sgInit
            (fun k => σ (k + initReads init))) i :=
  board_loop_steps sg_file hf b hb N

/-- The signed step's run from reset over the image file succeeds for every number of steps. -/
theorem sg_board_runs (σ : Nat → UInt32) (code : UInt32 → Option UInt16)
    (hf : Flash code sgBytes sgSize) (b : State) (hb : Reset code flashItcm b) :
    ∀ k, ∃ t, run platform σ code k b = some t :=
  board_loop_runs sg_file hf b hb

end TestSupport.M7.SignedBoardFile

#print axioms TestSupport.M7.SignedBoardFile.sg_board
#print axioms TestSupport.M7.SignedBoardFile.sg_board_runs
#print axioms TestSupport.M7.SignedBoardFile.sg_board_steps
#print axioms TestSupport.M7.SignedBoardFile.sg_file
#print axioms TestSupport.M7.Signed.board_loop
#print axioms TestSupport.M7.Signed.board_loop_steps
#print axioms TestSupport.M7.Signed.board_loop_runs
#print axioms TestSupport.M7.Signed.sg_static
#print axioms TestSupport.M7.Signed.sg_requests
#print axioms TestSupport.M7.Signed.sg_confined
#print axioms TestSupport.M7.Signed.sgCompiled.sgUsart3Tick.implements
#print axioms LeanExe.M7.sim_ltSI64
#print axioms LeanExe.M7.sim_leSI64
#print axioms LeanExe.M7.sim_shrSI64
#print axioms LeanExe.M7.Nucleo.board_run_steps
#print axioms LeanExe.M7.costRun_le_staticCost
