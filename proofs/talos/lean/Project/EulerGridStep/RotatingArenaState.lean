import Project.EulerGridStep.RotatingPool
import Project.EulerGridStep.LaterArenaState

namespace Project.EulerGridStep.Execution
open Wasm

def rotatingPool (base count completed : Nat) : List UInt64 :=
  if completed = 1 then writerPool (rotatingRoots base count completed) 0
  else reusePool (rotatingRoots base count completed) 0

def rotatingHeapSlot (completed : Nat) : Nat := if completed = 1 then 7 else 8

structure RotatingArenaState (current : Store Unit) (base cells completed : Nat) (output : Array UInt64)
    (allocs releases frees : UInt64) : Prop where
  buffers : BufferState current output.size [⟨rotatingRoots base output.size completed 0, output⟩]
    (rotatingPool base output.size completed) allocs releases frees
  heap : current.globals.globals[0]? = some (.i64 (arenaHeap base output.size (rotatingHeapSlot completed)))
  budget : base + (cells + 6) * arenaObjectSize output.size ≤ current.mem.pages * 65536

theorem RotatingArenaState.of_first {current : Store Unit} {base cells : Nat} {output : Array UInt64}
    {allocs releases frees : UInt64}
    (h : LaterArenaState current base cells 1 output allocs releases frees) :
    RotatingArenaState current base cells 1 output allocs releases frees := by
  refine ⟨?_, ?_, h.budget⟩
  · simpa [rotatingPool, rotatingRoots, rotatingSlot, laterSlot, writerPool] using h.buffers
  · simpa [rotatingHeapSlot] using h.heap

theorem RotatingArenaState.mixed {current : Store Unit} {base cells : Nat} {output : Array UInt64}
    {allocs releases frees : UInt64}
    (h : RotatingArenaState current base cells 1 output allocs releases frees)
    (cell : Project.EulerCellStep.Model.CheckedCell) (hLoop : 1 < cells) :
    MixedCellState current (arenaHeap base output.size 7) (rotatingRoots base output.size 1)
      output 1 cell 0 allocs releases frees := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [rotatingPool, ite_true, cellLive, show UInt64.ofNat 0 = 0 from rfl,
      UInt64.add_zero] using h.buffers
  · simpa [mixedHeap, rotatingHeapSlot] using h.heap
  · exact later_fresh_space current base output.size cells 1 hLoop h.buffers.pages h.budget

theorem RotatingArenaState.reused {current : Store Unit} {base cells completed : Nat} {output : Array UInt64}
    {allocs releases frees : UInt64}
    (h : RotatingArenaState current base cells completed output allocs releases frees)
    (cell : Project.EulerCellStep.Model.CheckedCell) (hCompleted : 2 ≤ completed) :
    ReusedCellState current (arenaHeap base output.size 8) (rotatingRoots base output.size completed)
      output completed cell 0 allocs releases frees := by
  refine ⟨?_, ?_⟩
  · simpa only [rotatingPool, show ¬completed = 1 by omega, ite_false, cellLive,
      show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] using h.buffers
  · simpa [rotatingHeapSlot, show ¬completed = 1 by omega] using h.heap

theorem RotatingArenaState.eight_slot_bound {current : Store Unit} {base cells completed : Nat}
    {output : Array UInt64} {allocs releases frees : UInt64}
    (h : RotatingArenaState current base cells completed output allocs releases frees)
    (hPositive : 0 < completed) (hLoop : completed < cells) :
    base + 8 * arenaObjectSize output.size ≤ 4294967296 := by
  have hMul := Nat.mul_le_mul_right (arenaObjectSize output.size) (by omega : 8 ≤ cells + 6)
  have hBudget := h.budget
  have hPages := h.buffers.pages
  omega

#print axioms RotatingArenaState.of_first
#print axioms RotatingArenaState.mixed
#print axioms RotatingArenaState.reused
#print axioms RotatingArenaState.eight_slot_bound
end Project.EulerGridStep.Execution
