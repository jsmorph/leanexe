import Project.EulerReconstructed.RetryBranches
import Project.EulerReconstructed.ControlRetry
import Project.EulerRiemann.RetryFailureResources
import Project.ProofKit.BlockLoop

namespace Project.EulerReconstructed.Execution
open Wasm Project.Runtime
open Project.EulerRiemann.Execution
open Project.EulerRiemann.Control (Attempt)
open Project.EulerRiemann.Traversal (Cell)

def RetryActive (n : Nat) (trials time alpha source need : UInt64) (grid : Array Cell)
    (expected : Attempt) (spare limit : Nat) (heap : Heap) (frame : Locals) : Prop :=
  ∃ fuel dt : UInt64,
    RetryFrameAt frame fuel n trials time dt alpha source 0 0 false ∧
    Control.retry fuel.toNat n trials.toNat time dt alpha grid = expected ∧
    heap.Reserved need (spare + 2) limit

def RetryTotalDone (initial : Store Unit) (initialHeap : Heap) (need : UInt64)
    (expected : Attempt) (spare limit : Nat) (store : Store Unit)
    (heap : Heap) (frame : Locals) : Prop :=
  ∃ result : FreeNode,
    RetryReturnedAt frame expected.status expected.dt result.root ∧
    heap.Owns store result expected.grid ∧ heap.Reserved need (spare + 1) limit ∧
    (expected.status = 0 → need ≤ result.capacity) ∧
    ∀ (saved : FreeNode) (grid : Array Cell), initialHeap.Owns initial saved grid →
      regionsDisjoint saved.region result.region

def retryTotalInvariant (initial : Store Unit) (initialHeap : Heap) (n : Nat)
    (trials time alpha source need : UInt64) (grid : Array Cell) (expected : Attempt)
    (spare limit pageLimit : Nat) (store : Store Unit) (frame : Locals) : Prop :=
  ∃ heap, RetryStoreAt initial initialHeap store heap ∧ store.mem.pages ≤ pageLimit ∧
    ((RetryActive n trials time alpha source need grid expected spare limit heap frame ∧
      RetryScratch frame) ∨ RetryTotalDone initial initialHeap need expected spare limit store heap frame)

def RetryTotalStopped (initial : Store Unit) (initialHeap : Heap) (n : Nat)
    (trials time alpha source need : UInt64) (grid : Array Cell) (expected : Attempt)
    (spare limit : Nat) (store : Store Unit) (heap : Heap) (frame : Locals) : Prop :=
  RetryTotalDone initial initialHeap need expected spare limit store heap frame ∨
    ∃ dt : UInt64, RetryFrameAt frame 0 n trials time dt alpha source 0 0 false ∧
      Control.retry 0 n trials.toNat time dt alpha grid = expected ∧
      heap.Reserved need (spare + 2) limit ∧ RetryScratch frame

def retryTotalIterationPost (initial : Store Unit) (initialHeap : Heap) (n : Nat)
    (trials time alpha source need : UInt64) (grid : Array Cell) (expected : Attempt)
    (spare limit pageLimit measure : Nat) : Assertion Unit :=
  Project.ProofKit.BlockLoop.stepPost
    (retryTotalInvariant initial initialHeap n trials time alpha source need grid expected spare limit pageLimit)
    (fun store frame => ∃ heap, RetryStoreAt initial initialHeap store heap ∧ store.mem.pages ≤ pageLimit ∧
      RetryTotalStopped initial initialHeap n trials time alpha source need grid expected spare limit store heap frame)
    (fun _ frame => retryMeasure frame) measure

theorem retryTotalInvariant.values {initial : Store Unit} {initialHeap : Heap} {n : Nat}
    {trials time alpha source need : UInt64} {grid : Array Cell} {expected : Attempt}
    {spare limit pageLimit : Nat} {store : Store Unit} {frame : Locals}
    (h : retryTotalInvariant initial initialHeap n trials time alpha source need grid expected
      spare limit pageLimit store frame) : frame.values = [] := by
  obtain ⟨heap, _, _, hActive | hDone⟩ := h
  · obtain ⟨⟨fuel, dt, hFrame, _⟩, _⟩ := hActive
    exact hFrame.values
  · obtain ⟨result, hFrame, _⟩ := hDone
    exact hFrame.values

theorem RetryTotalStopped.values {initial : Store Unit} {initialHeap : Heap} {n : Nat}
    {trials time alpha source need : UInt64} {grid : Array Cell} {expected : Attempt}
    {spare limit : Nat} {store : Store Unit} {heap : Heap} {frame : Locals}
    (h : RetryTotalStopped initial initialHeap n trials time alpha source need grid expected
      spare limit store heap frame) : frame.values = [] := by
  rcases h with hDone | ⟨dt, hFrame, _⟩
  · obtain ⟨result, hFrame, _⟩ := hDone
    exact hFrame.values
  · exact hFrame.values

theorem retry_loop_parts : retryLoop = retryLoop.take 7 ++
    (retryLoop.drop 7).take 8 ++
    [.localGet 16, .constI64 1, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
      .constI64 0, .eqI64, .eqz,
      .iff 0 0 retryTrial (retryFailureProgram 3 ++ [.constI64 1, .localSet 13]), .br 0] := rfl

#print axioms retryTotalInvariant.values
#print axioms RetryTotalStopped.values
#print axioms retry_loop_parts
end Project.EulerReconstructed.Execution
