import Project.EulerRiemann.AdvanceContinue

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

def gridCapacity (n : Nat) : UInt64 := normalizedCapacity (UInt64.ofNat (n * n)) 7

def AdvanceOrigin (initial : Store Unit) (initialHeap : Heap) (startTime time : UInt64)
    (source : FreeNode) (grid : Array Traversal.Cell) (tracked : Bool) : Prop :=
  if tracked then
    ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), initialHeap.Owns initial saved savedGrid →
      regionsDisjoint saved.region source.region
  else time = startTime ∧ initialHeap.Owns initial source grid

structure AdvanceCurrent (initial : Store Unit) (initialHeap : Heap) (n : Nat)
    (startTime time : UInt64) (store : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (tracked : Bool) : Prop where
  indexed : Traversal.Indexed n grid
  owner : heap.Owns store source grid
  capacity : gridCapacity n ≤ source.capacity
  origin : AdvanceOrigin initial initialHeap startTime time source grid tracked

def AdvanceActive (initial : Store Unit) (initialHeap : Heap) (n : Nat) (startTime : UInt64)
    (expected : Control.Result) (spare limit : Nat) (store : Store Unit) (heap : Heap) (frame : Locals) : Prop :=
  ∃ (fuel time : UInt64) (source : FreeNode) (grid : Array Traversal.Cell) (tracked : Bool),
    AdvanceFrameAt frame fuel n time source.root (if tracked then source.root else 0) 0 0 false ∧
    Control.advance fuel.toNat n time grid = expected ∧
    Time.endTime.toNat - time.toNat < fuel.toNat ∧
    AdvanceCurrent initial initialHeap n startTime time store heap source grid tracked ∧
    heap.Reserved (gridCapacity n) (spare + if tracked then 2 else 3) limit

def AdvanceDone (initial : Store Unit) (initialHeap : Heap) (n : Nat) (startTime : UInt64)
    (expected : Control.Result) (spare limit : Nat) (store : Store Unit) (heap : Heap) (frame : Locals) : Prop :=
  ∃ (fuel : UInt64) (source : FreeNode) (tracked : Bool),
    AdvanceFrameAt frame fuel n expected.time source.root (if tracked then source.root else 0)
      expected.time source.root true ∧
    expected.time = Time.endTime ∧
    AdvanceCurrent initial initialHeap n startTime expected.time store heap source expected.grid tracked ∧
    heap.Reserved (gridCapacity n) (spare + 2) limit

def advanceInvariant (initial : Store Unit) (initialHeap : Heap) (n : Nat) (startTime : UInt64)
    (expected : Control.Result) (spare limit : Nat) (store : Store Unit) (frame : Locals) : Prop :=
  ∃ heap, RetryStoreAt initial initialHeap store heap ∧
    (AdvanceActive initial initialHeap n startTime expected spare limit store heap frame ∨
      AdvanceDone initial initialHeap n startTime expected spare limit store heap frame)

theorem advanceInvariant.values {initial : Store Unit} {initialHeap : Heap} {n : Nat} {startTime : UInt64}
    {expected : Control.Result} {spare limit : Nat} {store : Store Unit} {frame : Locals}
    (h : advanceInvariant initial initialHeap n startTime expected spare limit store frame) : frame.values = [] := by
  obtain ⟨heap, _, hActive | hDone⟩ := h
  · obtain ⟨fuel, time, source, grid, tracked, hFrame, _⟩ := hActive
    exact hFrame.values
  · obtain ⟨fuel, source, tracked, hFrame, _⟩ := hDone
    exact hFrame.values

theorem advance_loop_parts : advanceLoop = advanceLoop.take 7 ++
    (advanceLoop.drop 7).take 2 ++
    [.localGet 2, .localGet 11, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 1, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 0, .eqI64, .eqz,
      .iff 0 0 advanceFinishBody advanceWorkBody, .br 0] := rfl

#print axioms advanceInvariant.values
#print axioms advance_loop_parts

end Project.EulerRiemann.Execution
