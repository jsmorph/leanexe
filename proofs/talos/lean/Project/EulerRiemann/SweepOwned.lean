import Project.EulerRiemann.ExecutionSweep
import Project.EulerRiemann.HeapGrid

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

theorem sweep_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (axis : Bool) (ratio : UInt64)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ 65536)
    (hBump : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat grid.size) 7) heap.nodes = none →
      heap.top.toNat + 48 + (8 + grid.size * 56) < 4294967296 ∧
      bumpPages heap.top (normalizedCapacity (UInt64.ofNat grid.size) 7) ≤
        initial.memoryCap Project.EulerRiemann.«module» 0) :
    let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    let node := allocatedNode heap.top need heap.nodes
    TerminatesWith env Project.EulerRiemann.«module» 70 initial
      [.i64 source.root, .i64 source.root, .i64 ratio, .i64 (boolWord axis), .i64 (UInt64.ofNat n)]
      (fun final values => values = [.i64 node.root, .i64 node.root] ∧
        (heap.allocate need).At final ∧
        (heap.allocate need).Owns final source grid ∧
        (heap.allocate need).Owns final node (Traversal.sweep n axis ratio grid) ∧
        regionsDisjoint source.region node.region ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap Project.EulerRiemann.«module» 0 = initial.memoryCap Project.EulerRiemann.«module» 0 ∧
        Memory.WritesGrid (heap.allocateStore initial need) final node.root grid.size) := by
  let need := normalizedCapacity (UInt64.ofNat grid.size) 7
  let node := allocatedNode heap.top need heap.nodes
  have hSize : grid.size ≤ 640000 := by
    rw [hIndexed.1]
    exact Nat.mul_le_mul hn.2 hn.2
  have hWord := UInt64.toNat_ofNat_of_lt' hOwner.buffer.values.size_lt
  have hNeed : need.toNat = 8 + grid.size * 56 := by
    simpa only [hWord] using sweep_capacity_toNat (UInt64.ofNat grid.size) (by omega)
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := by
    intro hNone
    have := (hBump hNone).1
    omega
  have hSourceRoot := hOwner.buffer.rootBound
  have hSourceCapacity := hOwner.buffer.capacity
  have hSourceHeap := hOwner.below
  have hSep : gridFreeSeparated source.root grid.size heap.nodes := by
    intro other hOther
    have hDisjoint := hOwner.separated other hOther
    have hOtherRoot := (hHeap.freeList.mem_bounds hOther).1
    simp only [regionsDisjoint, FreeNode.region] at hDisjoint
    omega
  have hCall := sweep_exact env initial n axis ratio source.root source.root heap.top heap.allocations
    grid heap.nodes hn hIndexed hOwner.buffer.values
    (by simp [hHeap.globals, Heap.globals]) (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals]) hHeap.freeList hSep (by omega) hPages
    (fun hNone => ⟨Nat.le_of_lt (hBump hNone).1, (hBump hNone).2⟩)
  apply hCall.mono
  intro final values hResult
  obtain ⟨hValues, _, hOutput, hWrites⟩ := hResult
  obtain ⟨hRoot, hCapacity, hStrict, hMemory, hFresh, hList, _, hNodeSep, hTotal⟩ :=
    sweep_resources initial final heap.top heap.allocations grid.size heap.nodes hSize
      hHeap.freeList hHeap.below (fun hNone => (hBump hNone).1) hWrites
  have hAllocatedHeap := heap.allocate_at initial need hHeap hFit
  have hBelow := allocated_below_top heap.top need heap.nodes hHeap.below hFit
  have hDisjoint := allocated_region_disjoint heap.top need source heap.nodes hSourceRoot
    hOwner.separated hOwner.below hFit
  refine ⟨hValues, ⟨?_, hList, hAllocatedHeap.below⟩, ?_, ?_, hDisjoint, ?_, ?_, hTotal⟩
  · rw [hTotal.globals]
    exact heap.allocate_globals initial need hHeap
  · exact hOwner.swept need grid.size hHeap (by omega) hFit hTotal
  · exact ⟨⟨hRoot, by simpa only [Traversal.sweep_size] using hCapacity,
      hStrict, hMemory, hFresh, hOutput⟩, hBelow.1, hNodeSep⟩
  · rw [hTotal.2.1]
    exact allocated_pages_le initial heap.top need heap.nodes hPages hFit
  · exact (hTotal.memoryCap Project.EulerRiemann.«module» 0).trans
      (heap.allocateStore_memoryCap initial need Project.EulerRiemann.«module» 0)

#print axioms sweep_owned

end Project.EulerRiemann.Execution
