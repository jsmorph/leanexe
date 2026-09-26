import Project.EulerRiemann.FrozenInitialGrowthExecute
import Project.EulerRiemann.FrozenInitialExtractResources
import Project.EulerRiemann.FrozenInitialGuard
import Project.ProofKit.BlockLoop

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit

def InitialActive (initial : Store Unit) (initialHeap : Heap) (n size limit : Nat)
    (store : Store Unit) (heap : Heap) (frame : Locals) : Prop :=
  ∃ (fuel : UInt64) (rounds : Nat) (source : FreeNode) (tracked : Bool) (grid : Array Traversal.Cell),
    InitialFrameAt frame fuel n size source.root (if tracked then source.root else 0) 0 false ∧
    InitialScratch frame ∧ rounds + fuel.toNat = 20 ∧ InitialPrefix n (2 ^ rounds) grid ∧
    heap.Owns store source grid ∧ source.capacity.toNat = initialBytes grid.size ∧
    InitialFreeBelow (min size grid.size) heap.nodes ∧
    heap.top.toNat + initialRemainingBytes grid.size fuel.toNat size ≤ limit ∧
    (tracked = true → ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell),
      initialHeap.Owns initial saved savedGrid → regionsDisjoint saved.region source.region)

def InitialResult (initial : Store Unit) (initialHeap : Heap) (n size limit : Nat)
    (store : Store Unit) (heap : Heap) (frame : Locals) (done : Bool) : Prop :=
  ∃ (fuel source tracker : UInt64) (result : FreeNode) (grid : Array Traversal.Cell),
    InitialFrameAt frame fuel n size source tracker result.root done ∧
    heap.Owns store result grid ∧ InitialPrefix n size grid ∧
    result.capacity.toNat = initialBytes size ∧ heap.top.toNat ≤ limit ∧
    (∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell),
      initialHeap.Owns initial saved savedGrid → regionsDisjoint saved.region result.region)

def initialInvariant (initial : Store Unit) (initialHeap : Heap) (n size limit pageLimit : Nat)
    (store : Store Unit) (frame : Locals) : Prop :=
  ∃ heap, RetryStoreAt initial initialHeap store heap ∧ store.mem.pages ≤ pageLimit ∧
    (InitialActive initial initialHeap n size limit store heap frame ∨
      InitialResult initial initialHeap n size limit store heap frame true)

def initialStopped (frame : Locals) : Prop :=
  frame.params[0]? = some (.i64 0) ∨ frame.locals[3]? = some (.i64 1)

def initialExit (initial : Store Unit) (initialHeap : Heap) (n size limit pageLimit : Nat)
    (store : Store Unit) (frame : Locals) : Prop :=
  initialInvariant initial initialHeap n size limit pageLimit store frame ∧ initialStopped frame

theorem initialInvariant.values {initial store : Store Unit} {initialHeap : Heap}
    {n size limit pageLimit : Nat} {frame : Locals}
    (h : initialInvariant initial initialHeap n size limit pageLimit store frame) : frame.values = [] := by
  obtain ⟨heap, _, _, hActive | hDone⟩ := h
  · obtain ⟨fuel, rounds, source, tracked, grid, hFrame, _⟩ := hActive
    exact hFrame.values
  · obtain ⟨fuel, source, tracker, result, grid, hFrame, _⟩ := hDone
    exact hFrame.values

#print axioms initialInvariant.values

end Project.EulerRiemann.Frozen.Execution
