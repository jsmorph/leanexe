import Project.EulerRiemann.ExecutionStep
import Project.EulerRiemann.HeapReserve

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

theorem stepAllocation_reserved (heap : Heap) (need : UInt64) (accepted : Bool)
    (spare limit : Nat) (h : heap.Reserved need (spare + 2) limit)
    (hLimit : limit ≤ 4294967296) :
    (stepAllocation heap need accepted).1.Reserved need (spare + 1) limit ∧
      need ≤ (stepAllocation heap need accepted).2.capacity := by
  have hFirst : (heap.allocate need).Reserved need (spare + 1) limit := by
    simpa using h.allocate (by omega) hLimit
  have hFirstCapacity : need ≤ (allocatedNode heap.top need heap.nodes).capacity :=
    UInt64.le_iff_toNat_le.mpr (allocated_capacity need heap.nodes)
  cases accepted with
  | false => exact ⟨hFirst, hFirstCapacity⟩
  | true =>
    have hSecond : ((heap.allocate need).allocate need).Reserved need spare limit := by
      simpa using hFirst.allocate (by omega) hLimit
    exact ⟨hSecond.release _ hFirstCapacity,
      UInt64.le_iff_toNat_le.mpr (allocated_capacity need (heap.allocate need).nodes)⟩

theorem stepAllocation_release_reserved (heap : Heap) (need : UInt64) (accepted : Bool)
    (spare limit : Nat) (h : heap.Reserved need (spare + 2) limit)
    (hLimit : limit ≤ 4294967296) :
    ((stepAllocation heap need accepted).1.release
      (stepAllocation heap need accepted).2).Reserved need (spare + 2) limit := by
  obtain ⟨hReserved, hCapacity⟩ := stepAllocation_reserved heap need accepted spare limit h hLimit
  exact hReserved.release _ hCapacity

theorem step_reserved (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (ratio : UInt64)
    (spare limit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerRiemann.«module» 0 * 65536) :
    let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    let result := stepAllocation heap need (Traversal.accepted (Traversal.sweep n false ratio grid))
    TerminatesWith env Project.EulerRiemann.«module» 73 initial
      [.i64 source.root, .i64 source.root, .i64 ratio, .i64 (UInt64.ofNat n)]
      (fun final values => values = [.i64 result.2.root, .i64 result.2.root] ∧
        result.1.At final ∧ result.1.Owns final result.2 (Traversal.step n ratio grid) ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap Project.EulerRiemann.«module» 0 = initial.memoryCap Project.EulerRiemann.«module» 0 ∧
        result.1.Reserved need (spare + 1) limit ∧ need ≤ result.2.capacity ∧
        ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns initial saved savedGrid →
          result.1.Owns final saved savedGrid ∧ regionsDisjoint saved.region result.2.region) := by
  have hSize : grid.size ≤ 640000 := by
    rw [hIndexed.1]
    exact Nat.mul_le_mul hn.2 hn.2
  have hWord := UInt64.toNat_ofNat_of_lt' hOwner.buffer.values.size_lt
  have hNeed : (normalizedCapacity (UInt64.ofNat grid.size) 7).toNat = 8 + grid.size * 56 := by
    simpa only [hWord] using sweep_capacity_toNat (UInt64.ofNat grid.size) (by omega)
  have hAfter : (heap.allocate (normalizedCapacity (UInt64.ofNat grid.size) 7)).Reserved
      (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 1) limit := by
    simpa using hReserve.allocate (by omega) (Nat.le_of_lt hLimit)
  apply (step_exact env initial heap source grid n ratio hn hIndexed hHeap hOwner hPages
    (by simpa only [hNeed] using hReserve.bump_fits (by omega) hLimit hCap)
    (by simpa only [hNeed] using hAfter.bump_fits (by omega) hLimit hCap)).mono
  intro final values hResult
  obtain ⟨hValues, hHeapFinal, hOwnerFinal, hPagesFinal, hCapFinal, hFrame⟩ := hResult
  obtain ⟨hReserved, hCapacity⟩ := stepAllocation_reserved heap _ _ spare limit hReserve (Nat.le_of_lt hLimit)
  exact ⟨hValues, hHeapFinal, hOwnerFinal, hPagesFinal, hCapFinal, hReserved, hCapacity, hFrame⟩

#print axioms stepAllocation_reserved
#print axioms stepAllocation_release_reserved
#print axioms step_reserved

end Project.EulerRiemann.Execution
