import Project.EulerRiemann.FrozenOwnedWords

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.Clob Project.ProofKit

theorem Heap.finishWords (heap : Heap) (initial final : Store Unit) (need : UInt64)
    (words : Array UInt64) (hHeap : heap.At initial)
    (hNeed : 8 * (words.size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hWrites : ProofKit.Memory.WritesRange (heap.allocateArrayStore initial need 1) final
      (allocatedRoot heap.top need heap.nodes).toNat
      ((allocatedRoot heap.top need heap.nodes).toNat + 8 * (words.size + 1)))
    (hWords : UInt64Array.At final (allocatedRoot heap.top need heap.nodes) words) :
    (heap.allocate need).At final ∧
      (heap.allocate need).OwnsWords final (allocatedNode heap.top need heap.nodes) words := by
  let node := allocatedNode heap.top need heap.nodes
  let allocated := heap.allocateArrayStore initial need 1
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun hNone => (hBump hNone).le
  have hAllocatedHeap := heap.allocateArrayStore_at initial need 1 hHeap hFit
  have hBounds := allocated_bounds initial heap.top need heap.nodes hHeap.freeList hFit
  have hCapacity : 8 * (words.size + 1) ≤ node.capacity.toNat :=
    hNeed.trans (allocated_capacity need heap.nodes)
  have hRoot : 48 ≤ node.root.toNat := hBounds.1
  have hStrict : node.root.toNat + node.capacity.toNat < 4294967296 :=
    allocated_strict_bound initial heap.top need heap.nodes hHeap.freeList hBump
  have hMemory : node.root.toNat + node.capacity.toNat ≤ allocated.mem.pages * 65536 := by
    change node.root.toNat + node.capacity.toNat ≤
      (FixedArrayAllocate.allocated initial heap.top need 1 heap.nodes).mem.pages * 65536
    rw [arrayAllocated_pages]
    exact hBounds.2.2
  have hFresh : FreshFixedArrayAt allocated node.root node.capacity 1 :=
    arrayAllocated_fresh initial heap.top need 1 heap.nodes hHeap.freeList hFit
  have hSeparated := allocated_node_separated initial heap.top need heap.nodes
    hHeap.freeList hHeap.below hFit
  change ProofKit.Memory.WritesRange allocated final node.root.toNat
    (node.root.toNat + 8 * (words.size + 1)) at hWrites
  have hFinalHeap : (heap.allocate need).At final := by
    refine ⟨?_, ?_, hAllocatedHeap.below⟩
    · rw [hWrites.1]
      exact hAllocatedHeap.globals
    · apply FreeListMemory.frame_headers hAllocatedHeap.freeList hWrites.2.1.ge
      intro other hOther address hLow hHigh
      have hOtherRoot := (hAllocatedHeap.freeList.mem_bounds hOther).1
      have hSep := hSeparated other hOther
      change regionsDisjoint node.region other.region at hSep
      simp only [regionsDisjoint, FreeNode.region] at hSep
      exact hWrites.2.2 address (by omega)
  refine ⟨hFinalHeap, ⟨⟨hRoot, hCapacity, hStrict, ?_, ?_, hWords⟩, ?_, hSeparated⟩⟩
  · rw [hWrites.2.1]
    exact hMemory
  · apply hFresh.frame (by omega) hRoot (Nat.le_refl node.root.toNat)
    intro address hHigh
    exact hWrites.2.2 address (Or.inl hHigh)
  · exact (allocated_below_top heap.top need heap.nodes hHeap.below hFit).1

theorem release_words_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (node : FreeNode) (words : Array UInt64)
    (hHeap : heap.At initial) (hOwner : heap.OwnsWords initial node words) :
    TerminatesWith env Project.EulerRiemann.Frozen.«module» 107 initial [.i64 node.root]
      (fun final values => values = [] ∧ final = heap.releaseStore initial node ∧
        (heap.release node).At final) := by
  obtain ⟨hMagic, hRc, hCapacity, hKind, hStride, hMask⟩ := hOwner.buffer.fresh
  have hBounds := hOwner.buffer.values.1
  have hFits := hOwner.buffer.values.2.1
  have hCall := Project.Runtime.release_frees_fixed_array_zero_mask_full env
    Project.EulerRiemann.Frozen.«module» 107 initial node.root (freeHead heap.nodes)
    heap.releases heap.frees words.size 1 (typeIdx := some 107) rfl (by decide)
    (by omega) (by decide) hOwner.buffer.rootBound (by omega) (by omega)
    hMagic hRc hKind hOwner.buffer.values.lengthRead hStride hMask
    (by simp [hHeap.globals, Heap.globals]) (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals])
  apply hCall.mono
  rintro final values ⟨hValues, hMem, hGlobals, hStore⟩
  have hGlobals' : final.globals =
      { globals := ((initial.globals.globals.set 4 (.i64 (heap.releases + 1))).set 5
        (.i64 (heap.frees + 1))).set 1 (.i64 node.root) } := congrArg Globals.mk hGlobals
  have hFinal : final = heap.releaseStore initial node := by
    rw [hStore, hMem, hGlobals']
    rfl
  refine ⟨hValues, hFinal, ?_⟩
  rw [hFinal]
  exact heap.release_at initial node hHeap hOwner.buffer.rootBound
    hOwner.buffer.addressBound hOwner.buffer.memoryBound hCapacity hOwner.below hOwner.separated

#print axioms Heap.finishWords
#print axioms release_words_owned

end Project.EulerRiemann.Frozen.Execution
