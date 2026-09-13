import Project.EulerRiemann.AdvanceTotalFrame
import Project.EulerRiemann.AdvanceReplace

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

def AdvanceTotalDone (initial : Store Unit) (initialHeap : Heap) (n : Nat) (startTime : UInt64)
    (expected : Control.Result) (spare limit : Nat) (store : Store Unit) (heap : Heap) (frame : Locals) : Prop :=
  ∃ (source : FreeNode) (tracked : Bool),
    AdvanceReturnedAt frame expected.status expected.time source.root ∧
    AdvanceCurrent initial initialHeap n startTime expected.time store heap source expected.grid tracked ∧
    heap.Reserved (gridCapacity n) (spare + 1) limit

def advanceTotalInvariant (initial : Store Unit) (initialHeap : Heap) (n : Nat) (startTime : UInt64)
    (expected : Control.Result) (spare limit pageLimit : Nat) (store : Store Unit) (frame : Locals) : Prop :=
  ∃ heap, RetryStoreAt initial initialHeap store heap ∧ store.mem.pages ≤ pageLimit ∧
    (AdvanceActive initial initialHeap n startTime expected spare limit store heap frame ∨
      AdvanceTotalDone initial initialHeap n startTime expected spare limit store heap frame)

theorem advanceTotalInvariant.values {initial : Store Unit} {initialHeap : Heap} {n : Nat}
    {startTime : UInt64} {expected : Control.Result} {spare limit pageLimit : Nat} {store : Store Unit} {frame : Locals}
    (h : advanceTotalInvariant initial initialHeap n startTime expected spare limit pageLimit store frame) :
    frame.values = [] := by
  obtain ⟨heap, _, _, hActive | hDone⟩ := h
  · obtain ⟨fuel, time, source, grid, tracked, hFrame, _⟩ := hActive
    exact hFrame.values
  · obtain ⟨source, tracked, hFrame, _⟩ := hDone
    exact hFrame.values

theorem AdvanceCurrent.preserved {initial current final : Store Unit} {initialHeap heap finalHeap : Heap}
    {n : Nat} {startTime time : UInt64} {source : FreeNode} {grid : Array Traversal.Cell} {tracked : Bool}
    (h : AdvanceCurrent initial initialHeap n startTime time current heap source grid tracked)
    (hNext : RetryStoreAt current heap final finalHeap) :
    AdvanceCurrent initial initialHeap n startTime time final finalHeap source grid tracked :=
  ⟨h.indexed, hNext.held source grid h.owner, h.capacity, h.origin⟩

#print axioms advanceTotalInvariant.values
#print axioms AdvanceCurrent.preserved

end Project.EulerRiemann.Execution
