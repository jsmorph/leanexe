import Project.EulerRiemann.RetryGuard
import Project.EulerRiemann.ControlRetry

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

structure RetryStoreAt (initial : Store Unit) (initialHeap : Heap)
    (store : Store Unit) (heap : Heap) : Prop where
  heapState : heap.At store
  pages : store.mem.pages ≤ 65536
  cap : store.memoryCap Project.EulerRiemann.«module» 0 = initial.memoryCap Project.EulerRiemann.«module» 0
  held : ∀ (saved : FreeNode) (grid : Array Traversal.Cell), initialHeap.Owns initial saved grid →
    heap.Owns store saved grid

def RetryActive (n : Nat) (time source need : UInt64) (grid : Array Traversal.Cell)
    (expected : Control.Attempt) (spare limit : Nat) (heap : Heap) (frame : Locals) : Prop :=
  ∃ fuel dt : UInt64,
    RetryFrameAt frame fuel n time dt source 0 0 false ∧
    Control.retry fuel.toNat n time dt grid = expected ∧ heap.Reserved need (spare + 2) limit

def RetryDone (initial : Store Unit) (initialHeap : Heap) (n : Nat) (time source need : UInt64)
    (expected : Control.Attempt) (spare limit : Nat) (store : Store Unit)
    (heap : Heap) (frame : Locals) : Prop :=
  ∃ (fuel dt : UInt64) (result : FreeNode),
    RetryFrameAt frame fuel n time dt source expected.dt result.root true ∧
    heap.Owns store result expected.grid ∧ heap.Reserved need (spare + 1) limit ∧
    need ≤ result.capacity ∧
    ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), initialHeap.Owns initial saved savedGrid →
      regionsDisjoint saved.region result.region

def retryInvariant (initial : Store Unit) (initialHeap : Heap) (n : Nat)
    (time source need : UInt64) (grid : Array Traversal.Cell) (expected : Control.Attempt)
    (spare limit : Nat) (store : Store Unit) (frame : Locals) : Prop :=
  ∃ heap, RetryStoreAt initial initialHeap store heap ∧
    (RetryActive n time source need grid expected spare limit heap frame ∨
      RetryDone initial initialHeap n time source need expected spare limit store heap frame)

theorem retry_loop_parts : retryLoop = retryLoop.take 7 ++
    (retryLoop.drop 7).take 8 ++
    [.localGet 14, .constI64 1, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
      .constI64 0, .eqI64, .eqz,
      .iff 0 0 retryTrial
        (match (retryLoop[22]? : Option Wasm.Instruction) with
          | some (.iff _ _ _ no _ _) => no | _ => []), .br 0] := rfl

theorem retry_success_nonzero (fuel : UInt64) (n : Nat) (time dt : UInt64)
    (grid : Array Traversal.Cell) (h : (Control.retry fuel.toNat n time dt grid).status = 0) :
    fuel ≠ 0 := by
  intro hZero
  simp [hZero, Control.retry] at h

theorem retryFuel_unfold (fuel : UInt64) (hFuel : fuel ≠ 0) :
    fuel.toNat = (fuel - 1).toNat + 1 := by
  have hDecrease := retryFuel_decreases fuel hFuel
  have hOne : (1 : UInt64).toNat = 1 := rfl
  have hPositive : 1 ≤ fuel.toNat := by omega
  rw [UInt64.toNat_sub_of_le _ _
    (by simpa only [UInt64.le_iff_toNat_le, hOne] using hPositive), hOne]
  omega

#print axioms retry_loop_parts
#print axioms retry_success_nonzero
#print axioms retryFuel_unfold

end Project.EulerRiemann.Execution
