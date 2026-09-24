import Project.ClobDepth.Heap

namespace Project.ClobDepth.HeapProof
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit
  Project.ClobDepth.Model Project.ClobDepth.Representation Project.EulerRiemann.Execution

/-- Releasing a uniquely owned level array executes the actual recursive
release export and installs its chunk at the free-list head. -/
theorem release_exact (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (node : FreeNode) (levels : List LevelL) (hHeap : heap.At store)
    (hOwner : OwnsLevels heap store node levels) :
    TerminatesWith env Project.ClobDepth.module 11 store [.i64 node.root]
      (fun final values => values = [] ∧ final = heap.releaseStore store node) := by
  have hCapacity := hOwner.buffer.capacity
  have hAddress := hOwner.buffer.addressBound
  have hFit := hOwner.buffer.memoryBound
  unfold fixedArrayBytes at hCapacity
  apply FixedArrayRelease.exact env Project.ClobDepth.module 11 store node.root node.capacity
    (freeHead heap.nodes) heap.releases heap.frees levels.length 2
    (typeIdx := some 11) rfl rfl (by omega) (by decide) hOwner.buffer.rootBound (by omega)
    (by omega) hOwner.buffer.contents.1
  · simpa only [toUInt32_eq_ofNat] using hOwner.buffer.contents.2.1.1
  · simp [hHeap.globals, Heap.globals]
  · simp [hHeap.globals, Heap.globals]
  · simp [hHeap.globals, Heap.globals]

theorem release_heap (store : Store Unit) (heap : Heap) (node : FreeNode)
    (levels : List LevelL) (hHeap : heap.At store) (hOwner : OwnsLevels heap store node levels) :
    (heap.release node).At (heap.releaseStore store node) := by
  exact heap.release_at store node hHeap hOwner.buffer.rootBound hOwner.buffer.addressBound
    hOwner.buffer.memoryBound hOwner.buffer.contents.1.2.2.1 hOwner.below hOwner.separated

theorem OwnsLevels.released {heap : Heap} {store : Store Unit} {source : FreeNode}
    {levels : List LevelL} (hOwner : OwnsLevels heap store source levels) (node : FreeNode)
    (hRoot : 48 ≤ node.root.toNat) (hRoot32 : node.root.toNat ≤ 4294967296)
    (hSep : regionsDisjoint source.region node.region) :
    OwnsLevels (heap.release node) (heap.releaseStore store node) source levels := by
  refine ⟨hOwner.buffer.frame rfl ?_, hOwner.below, ?_⟩
  · intro address hLow hHigh
    have hSourceRoot := hOwner.buffer.rootBound
    simp only [regionsDisjoint, FreeNode.region] at hSep
    exact releasedStore_bytes store node.root (freeHead heap.nodes) heap.releases heap.frees
      hRoot hRoot32 address (by omega)
  · intro other hOther
    rcases List.mem_cons.mp hOther with rfl | hOther
    · exact hSep
    · exact hOwner.separated other hOther

#print axioms release_exact
#print axioms release_heap
#print axioms OwnsLevels.released
end Project.ClobDepth.HeapProof
