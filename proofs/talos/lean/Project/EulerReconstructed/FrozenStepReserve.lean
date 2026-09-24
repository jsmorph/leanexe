import Project.EulerReconstructed.FrozenExecutionStep
import Project.EulerRiemann.FrozenStepReserve

namespace Project.EulerReconstructed.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity
open Project.EulerRiemann.Frozen
open Project.EulerRiemann.Frozen.Execution

theorem step_pages_reserved (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Frozen.Traversal.Cell) (n : Nat) (fuel ratio : UInt64)
    (spare limit pageLimit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Frozen.Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerReconstructed.Frozen.«module» 0 * 65536)
    (hLimitPages : limit ≤ pageLimit * 65536) :
    let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    let result := stepAllocation heap need (Project.EulerRiemann.Frozen.Traversal.accepted (Traversal.sweep n fuel.toNat false ratio grid))
    TerminatesWith env Project.EulerReconstructed.Frozen.«module» 124 initial
      [.i64 source.root, .i64 source.root, .i64 ratio, .i64 fuel, .i64 (UInt64.ofNat n)]
      (fun final values => values = [.i64 result.2.root, .i64 result.2.root] ∧
        result.1.At final ∧ result.1.Owns final result.2 (Traversal.step n fuel.toNat ratio grid) ∧
        final.mem.pages ≤ pageLimit ∧
        final.memoryCap Project.EulerReconstructed.Frozen.«module» 0 = initial.memoryCap Project.EulerReconstructed.Frozen.«module» 0 ∧
        result.1.Reserved need (spare + 1) limit ∧ need ≤ result.2.capacity ∧
        ∀ (saved : FreeNode) (savedGrid : Array Project.EulerRiemann.Frozen.Traversal.Cell), heap.Owns initial saved savedGrid →
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
  apply (step_pages_exact env initial heap source grid n fuel ratio pageLimit hn hIndexed hHeap hOwner hPages hPageLimit
    (by simpa only [hNeed] using hReserve.bump_fits (by omega) hLimit hCap)
    (by simpa only [hNeed] using hAfter.bump_fits (by omega) hLimit hCap)
    (fun hNone => (hReserve.bump_bound (by omega) hNone).trans hLimitPages)
    (fun hNone => (hAfter.bump_bound (by omega) hNone).trans hLimitPages)).mono
  intro final values hResult
  obtain ⟨hValues, hHeapFinal, hOwnerFinal, hPagesFinal, hCapFinal, hFrame⟩ := hResult
  obtain ⟨hReserved, hCapacity⟩ := stepAllocation_reserved heap _ _ spare limit hReserve (Nat.le_of_lt hLimit)
  exact ⟨hValues, hHeapFinal, hOwnerFinal, hPagesFinal, hCapFinal, hReserved, hCapacity, hFrame⟩

theorem step_reserved (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Frozen.Traversal.Cell) (n : Nat) (fuel ratio : UInt64)
    (spare limit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Frozen.Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerReconstructed.Frozen.«module» 0 * 65536) :
    let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    let result := stepAllocation heap need (Project.EulerRiemann.Frozen.Traversal.accepted (Traversal.sweep n fuel.toNat false ratio grid))
    TerminatesWith env Project.EulerReconstructed.Frozen.«module» 124 initial
      [.i64 source.root, .i64 source.root, .i64 ratio, .i64 fuel, .i64 (UInt64.ofNat n)]
      (fun final values => values = [.i64 result.2.root, .i64 result.2.root] ∧
        result.1.At final ∧ result.1.Owns final result.2 (Traversal.step n fuel.toNat ratio grid) ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap Project.EulerReconstructed.Frozen.«module» 0 = initial.memoryCap Project.EulerReconstructed.Frozen.«module» 0 ∧
        result.1.Reserved need (spare + 1) limit ∧ need ≤ result.2.capacity ∧
        ∀ (saved : FreeNode) (savedGrid : Array Project.EulerRiemann.Frozen.Traversal.Cell), heap.Owns initial saved savedGrid →
          result.1.Owns final saved savedGrid ∧ regionsDisjoint saved.region result.2.region) := by
  exact step_pages_reserved env initial heap source grid n fuel ratio spare limit 65536
    hn hIndexed hHeap hOwner hPages (Nat.le_refl _) hReserve hLimit hCap hLimit.le

#print axioms step_pages_reserved
#print axioms step_reserved

end Project.EulerReconstructed.Frozen.Execution
