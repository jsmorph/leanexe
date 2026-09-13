import Project.EulerRiemann.RetryTotalFrame
import Project.EulerRiemann.RetryFailureResources
import Project.ProofKit.BlockLoop

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

def RetryTotalDone (initial : Store Unit) (initialHeap : Heap) (need : UInt64)
    (expected : Control.Attempt) (spare limit : Nat) (store : Store Unit)
    (heap : Heap) (frame : Locals) : Prop :=
  ∃ result : FreeNode,
    RetryReturnedAt frame expected.status expected.dt result.root ∧
    heap.Owns store result expected.grid ∧ heap.Reserved need (spare + 1) limit ∧
    (expected.status = 0 → need ≤ result.capacity) ∧
    ∀ (saved : FreeNode) (grid : Array Traversal.Cell), initialHeap.Owns initial saved grid →
      regionsDisjoint saved.region result.region

def retryTotalInvariant (initial : Store Unit) (initialHeap : Heap) (n : Nat)
    (time source need : UInt64) (grid : Array Traversal.Cell) (expected : Control.Attempt)
    (spare limit pageLimit : Nat) (store : Store Unit) (frame : Locals) : Prop :=
  ∃ heap, RetryStoreAt initial initialHeap store heap ∧ store.mem.pages ≤ pageLimit ∧
    ((RetryActive n time source need grid expected spare limit heap frame ∧ RetryScratch frame) ∨
      RetryTotalDone initial initialHeap need expected spare limit store heap frame)

def RetryTotalStopped (initial : Store Unit) (initialHeap : Heap) (n : Nat)
    (time source need : UInt64) (grid : Array Traversal.Cell) (expected : Control.Attempt)
    (spare limit : Nat) (store : Store Unit) (heap : Heap) (frame : Locals) : Prop :=
  RetryTotalDone initial initialHeap need expected spare limit store heap frame ∨
    ∃ dt : UInt64, RetryFrameAt frame 0 n time dt source 0 0 false ∧
      Control.retry 0 n time dt grid = expected ∧
      heap.Reserved need (spare + 2) limit ∧ RetryScratch frame

def retryTotalIterationPost (initial : Store Unit) (initialHeap : Heap) (n : Nat)
    (time source need : UInt64) (grid : Array Traversal.Cell) (expected : Control.Attempt)
    (spare limit pageLimit measure : Nat) : Assertion Unit :=
  Project.ProofKit.BlockLoop.stepPost
    (retryTotalInvariant initial initialHeap n time source need grid expected spare limit pageLimit)
    (fun store frame => ∃ heap, RetryStoreAt initial initialHeap store heap ∧ store.mem.pages ≤ pageLimit ∧
      RetryTotalStopped initial initialHeap n time source need grid expected spare limit store heap frame)
    (fun _ frame => retryMeasure frame) measure

theorem retryTotalInvariant.values {initial : Store Unit} {initialHeap : Heap} {n : Nat}
    {time source need : UInt64} {grid : Array Traversal.Cell} {expected : Control.Attempt}
    {spare limit pageLimit : Nat} {store : Store Unit} {frame : Locals}
    (h : retryTotalInvariant initial initialHeap n time source need grid expected spare limit pageLimit store frame) :
    frame.values = [] := by
  obtain ⟨heap, _, _, hActive | hDone⟩ := h
  · obtain ⟨⟨fuel, dt, hFrame, _⟩, _⟩ := hActive
    exact hFrame.values
  · obtain ⟨result, hFrame, _⟩ := hDone
    exact hFrame.values

theorem RetryTotalStopped.values {initial : Store Unit} {initialHeap : Heap} {n : Nat}
    {time source need : UInt64} {grid : Array Traversal.Cell} {expected : Control.Attempt}
    {spare limit : Nat} {store : Store Unit} {heap : Heap} {frame : Locals}
    (h : RetryTotalStopped initial initialHeap n time source need grid expected spare limit store heap frame) :
    frame.values = [] := by
  rcases h with hDone | ⟨dt, hFrame, _⟩
  · obtain ⟨result, hFrame, _⟩ := hDone
    exact hFrame.values
  · exact hFrame.values

#print axioms retryTotalInvariant.values
#print axioms RetryTotalStopped.values

end Project.EulerRiemann.Execution
