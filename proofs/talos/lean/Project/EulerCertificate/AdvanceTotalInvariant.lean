import Project.EulerCertificate.AdvanceTotalFrame
import Project.EulerCertificate.AdvanceContinue
import Project.EulerRiemann.AdvanceTotalInvariant

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime
open Project.EulerRiemann
open Project.EulerRiemann.Execution
open Project.EulerCertificate.Control (Result)
open Project.EulerCertificate.Flux (Vector)

def AdvanceActive (initial : Store Unit) (initialHeap : Heap) (n : Nat) (trials startTime : UInt64)
    (expected : Result) (spare limit : Nat) (store : Store Unit) (heap : Heap) (frame : Locals) : Prop :=
  ∃ (fuel time : UInt64) (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell)
      (boundary : Vector) (tracked : Bool),
    AdvanceFrameAt frame fuel n trials time source.root (if tracked then source.root else 0) 0 0 false boundary ∧
    Control.advance fuel.toNat n trials.toNat time grid boundary = expected ∧
    Time.endTime.toNat - time.toNat < fuel.toNat ∧
    AdvanceCurrent initial initialHeap n startTime time store heap source grid tracked ∧
    heap.Reserved (gridCapacity n) (spare + if tracked then 2 else 3) limit

def AdvanceTotalDone (initial : Store Unit) (initialHeap : Heap) (n : Nat) (startTime : UInt64)
    (expected : Result) (spare limit : Nat) (store : Store Unit) (heap : Heap) (frame : Locals) : Prop :=
  ∃ (source : FreeNode) (tracked : Bool),
    AdvanceReturnedAt frame expected.status expected.time source.root expected.boundary ∧
    AdvanceCurrent initial initialHeap n startTime expected.time store heap source expected.grid tracked ∧
    heap.Reserved (gridCapacity n) (spare + 1) limit

def advanceTotalInvariant (initial : Store Unit) (initialHeap : Heap) (n : Nat) (trials startTime : UInt64)
    (expected : Result) (spare limit pageLimit : Nat) (store : Store Unit) (frame : Locals) : Prop :=
  ∃ heap, RetryStoreAt initial initialHeap store heap ∧ store.mem.pages ≤ pageLimit ∧
    (AdvanceActive initial initialHeap n trials startTime expected spare limit store heap frame ∨
      AdvanceTotalDone initial initialHeap n startTime expected spare limit store heap frame)

theorem advanceTotalInvariant.values {initial : Store Unit} {initialHeap : Heap} {n : Nat}
    {trials startTime : UInt64} {expected : Result} {spare limit pageLimit : Nat}
    {store : Store Unit} {frame : Locals}
    (h : advanceTotalInvariant initial initialHeap n trials startTime expected spare limit pageLimit store frame) :
    frame.values = [] := by
  obtain ⟨heap, _, _, hActive | hDone⟩ := h
  · obtain ⟨fuel, time, source, grid, boundary, tracked, hFrame, _⟩ := hActive
    exact hFrame.values
  · obtain ⟨source, tracked, hFrame, _⟩ := hDone
    exact hFrame.values

theorem advance_loop_parts : advanceLoop = advanceLoop.take 7 ++
    (advanceLoop.drop 7).take 2 ++
    [.localGet 3, .localGet 36, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 1, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 0, .eqI64, .eqz,
      .iff 0 0 advanceFinishBody advanceWorkBody, .br 0] := rfl

#print axioms advanceTotalInvariant.values
#print axioms advance_loop_parts
end Project.EulerCertificate.Execution
