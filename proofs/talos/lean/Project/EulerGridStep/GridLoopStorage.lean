import Project.EulerGridStep.ProtectedArenaAdvance
import Project.EulerGridStep.AdvanceRotatingRejected

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

def rotatingRejectedRoot (base count completed : Nat) : UInt64 :=
  if completed = 1 then arenaRoot base count 1 else rotatingRoots base count (completed - 1) 1

def rotatingRejectedPool (base count completed : Nat) : List UInt64 :=
  if completed = 1 then []
  else rotatingRoots base count (completed - 1) 0 :: rotatingPoolTail base count (completed - 1)

def rotatingRejectedHeapSlot (completed : Nat) : Nat :=
  if completed = 1 then 2 else rotatingHeapSlot (completed - 1)

structure RotatingRejectedState (current : Store Unit) (base cells completed : Nat) (output : Array UInt64)
    (allocs releases frees : UInt64) : Prop where
  buffers : BufferState current output.size [⟨rotatingRejectedRoot base output.size completed, output⟩]
    (rotatingRejectedPool base output.size completed) allocs releases frees
  heap : current.globals.globals[0]? = some (.i64 (arenaHeap base output.size (rotatingRejectedHeapSlot completed)))
  budget : base + (cells + 6) * arenaObjectSize output.size ≤ current.mem.pages * 65536
  status : output[0]! = 1

def gridLoopRoot (base count index : Nat) (status : UInt64) : UInt64 :=
  if index = 0 then arenaRoot base count 0
  else if status = 0 then rotatingRoots base count index 0 else rotatingRejectedRoot base count index

def gridLoopPool (base count index : Nat) (status : UInt64) : List UInt64 :=
  if index = 0 then []
  else if status = 0 then rotatingPool base count index else rotatingRejectedPool base count index

def gridLoopHeapSlot (index : Nat) (status : UInt64) : Nat :=
  if index = 0 then 1 else if status = 0 then rotatingHeapSlot index else rotatingRejectedHeapSlot index

/-- The three storage phases visited by the emitted outer loop. -/
inductive GridLoopStorage (current : Store Unit) (base cells : Nat) :
    Nat → Array UInt64 → UInt64 → UInt64 → UInt64 → Prop where
  | initial (allocs releases frees : UInt64)
      (buffers : BufferState current (1 + 6 * cells)
        [⟨arenaRoot base (1 + 6 * cells) 0, Array.replicate (1 + 6 * cells) 0⟩] [] allocs releases frees)
      (heap : current.globals.globals[0]? = some (.i64 (arenaHeap base (1 + 6 * cells) 1)))
      (budget : base + (cells + 6) * arenaObjectSize (1 + 6 * cells) ≤ current.mem.pages * 65536) :
      GridLoopStorage current base cells 0 (Array.replicate (1 + 6 * cells) 0) allocs releases frees
  | accepted (index : Nat) (output : Array UInt64) (allocs releases frees : UInt64)
      (positive : 0 < index) (status : output[0]! = 0)
      (arena : RotatingArenaState current base cells index output allocs releases frees) :
      GridLoopStorage current base cells index output allocs releases frees
  | rejected (index : Nat) (output : Array UInt64) (allocs releases frees : UInt64)
      (positive : 0 < index)
      (arena : RotatingRejectedState current base cells index output allocs releases frees) :
      GridLoopStorage current base cells index output allocs releases frees

theorem GridLoopStorage.buffers {current : Store Unit} {base cells index : Nat} {output : Array UInt64}
    {allocs releases frees : UInt64} (h : GridLoopStorage current base cells index output allocs releases frees) :
    BufferState current output.size [⟨gridLoopRoot base output.size index output[0]!, output⟩]
      (gridLoopPool base output.size index output[0]!) allocs releases frees := by
  cases h with
  | initial a r f hBuffers hHeap hBudget => simpa [gridLoopRoot, gridLoopPool] using hBuffers
  | accepted i out a r f hi hs hArena =>
      simpa only [gridLoopRoot, gridLoopPool, Nat.ne_of_gt hi, ite_false, hs, ite_true] using hArena.buffers
  | rejected i out a r f hi hArena =>
      simpa only [gridLoopRoot, gridLoopPool, Nat.ne_of_gt hi, ite_false, hArena.status,
        show ¬ (1 : UInt64) = 0 from by decide] using hArena.buffers

theorem GridLoopStorage.heap {current : Store Unit} {base cells index : Nat} {output : Array UInt64}
    {allocs releases frees : UInt64} (h : GridLoopStorage current base cells index output allocs releases frees) :
    current.globals.globals[0]? = some (.i64 (arenaHeap base output.size (gridLoopHeapSlot index output[0]!))) := by
  cases h with
  | initial a r f hBuffers hHeap hBudget => simpa [gridLoopHeapSlot] using hHeap
  | accepted i out a r f hi hs hArena =>
      simpa only [gridLoopHeapSlot, Nat.ne_of_gt hi, ite_false, hs, ite_true] using hArena.heap
  | rejected i out a r f hi hArena =>
      simpa only [gridLoopHeapSlot, Nat.ne_of_gt hi, ite_false, hArena.status,
        show ¬ (1 : UInt64) = 0 from by decide] using hArena.heap

theorem GridLoopStorage.budget {current : Store Unit} {base cells index : Nat} {output : Array UInt64}
    {allocs releases frees : UInt64} (h : GridLoopStorage current base cells index output allocs releases frees) :
    base + (cells + 6) * arenaObjectSize output.size ≤ current.mem.pages * 65536 := by
  cases h with
  | initial a r f hBuffers hHeap hBudget => simpa using hBudget
  | accepted i out a r f hi hs hArena => exact hArena.budget
  | rejected i out a r f hi hArena => exact hArena.budget

theorem GridLoopStorage.arrayAt {current : Store Unit} {base cells index : Nat} {output : Array UInt64}
    {allocs releases frees : UInt64} (h : GridLoopStorage current base cells index output allocs releases frees) :
    UInt64Array.At current (gridLoopRoot base output.size index output[0]!) output :=
  (h.buffers.liveAt ⟨gridLoopRoot base output.size index output[0]!, output⟩ (by simp)).2.2

#print axioms GridLoopStorage.buffers
#print axioms GridLoopStorage.heap
#print axioms GridLoopStorage.budget
#print axioms GridLoopStorage.arrayAt
end Project.EulerGridStep.Execution
