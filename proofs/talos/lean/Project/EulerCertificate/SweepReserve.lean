import Project.EulerCertificate.SolverMemory
import Project.EulerRiemann.HeapReserve
import Project.EulerRiemann.RetryResources

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity
open Project.EulerRiemann
open Project.EulerRiemann.Execution

theorem sweep_pages_reserved (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (trials : UInt64)
    (axis : Bool) (ratio : UInt64) (spare limit pageLimit : Nat)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 1) limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerCertificate.«module» 0 * 65536)
    (hLimitPages : limit ≤ pageLimit * 65536) :
    let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    let node := allocatedNode heap.top need heap.nodes
    let nextHeap := heap.allocate need
    TerminatesWith env Project.EulerCertificate.«module» 159 initial
      [.i64 source.root, .i64 source.root, .i64 ratio, .i64 (boolWord axis),
        .i64 trials, .i64 (UInt64.ofNat n)]
      (fun final values => values = [.i64 node.root, .i64 node.root] ∧
        RetryStoreAt initial heap final nextHeap ∧
        nextHeap.Owns final node (Project.EulerReconstructed.Traversal.sweep n trials.toNat axis ratio grid) ∧
        final.mem.pages ≤ pageLimit ∧ nextHeap.Reserved need spare limit ∧
        need ≤ node.capacity ∧
        ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns initial saved savedGrid →
          regionsDisjoint saved.region node.region) := by
  let need := normalizedCapacity (UInt64.ofNat grid.size) 7
  have hSize : grid.size ≤ 640000 := by
    rw [hIndexed.1]
    exact Nat.mul_le_mul hn.2 hn.2
  have hWord := UInt64.toNat_ofNat_of_lt' hOwner.buffer.values.size_lt
  have hNeed : (normalizedCapacity (UInt64.ofNat grid.size) 7).toNat = 8 + grid.size * 56 := by
    simpa only [hWord] using sweep_capacity_toNat (UInt64.ofNat grid.size) (by omega)
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 :=
    fun hNone => (hReserve.bump_bound (by omega) hNone).trans hLimit.le
  apply (sweep_pages_owned env initial heap source grid n trials axis ratio pageLimit
    hn hIndexed hHeap hOwner hPages hPageLimit
    (by simpa only [hNeed] using hReserve.bump_fits (by omega) hLimit hCap)
    (fun hNone => (hReserve.bump_bound (by omega) hNone).trans hLimitPages)).mono
  rintro final values ⟨hValues, hFinalHeap, _, hOutput, _, hFinalPages, hFinalCap, hWrites⟩
  refine ⟨hValues, ⟨hFinalHeap, hFinalPages.trans hPageLimit, hFinalCap, ?_⟩,
    hOutput, hFinalPages, ?_, UInt64.le_iff_toNat_le.mpr (allocated_capacity need heap.nodes), ?_⟩
  · intro saved savedGrid hSaved
    exact hSaved.swept need grid.size hHeap (by dsimp only [need]; rw [hNeed]; omega) hFit hWrites
  · simpa using hReserve.allocate (by omega) hLimit.le
  · intro saved savedGrid hSaved
    exact allocated_region_disjoint heap.top need saved heap.nodes hSaved.buffer.rootBound
      hSaved.separated hSaved.below hFit

#print axioms sweep_pages_reserved
end Project.EulerCertificate.Execution
