import Project.Gpt2QuantizedCached.CachedHidden.FinishRelease

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

theorem cleanup_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (params : List Value) (embedding updates hidden cache : FreeNode)
    (embeddingBytes updatesBytes hiddenBytes cacheBytes : ByteArray) (status : UInt64) (frame : Locals)
    (hParams : params.length = 8)
    (hMemory : Completion before original heap initial status hidden cache hiddenBytes cacheBytes)
    (hState : ResultFrame params embedding.root updates.root status (statusRoot status hidden)
      (statusRoot status cache) hiddenBytes.size cacheBytes.size frame)
    (hEmbedding : heap.OwnsPacked initial embedding embeddingBytes)
    (hUpdates : heap.OwnsPacked initial updates updatesBytes)
    (hEmbeddingFresh : before.FreshNode embedding) (hUpdatesFresh : before.FreshNode updates)
    (hTemporarySep : regionsDisjoint updates.region embedding.region)
    (hHiddenEmbedding : status = 0 → regionsDisjoint hidden.region embedding.region)
    (hHiddenUpdates : status = 0 → regionsDisjoint hidden.region updates.region)
    (hCacheEmbedding : status = 0 → regionsDisjoint cache.region embedding.region)
    (hCacheUpdates : status = 0 → regionsDisjoint cache.region updates.region)
    (Q : Assertion Unit) (rest : Program)
    (hNext : Completion before original ((heap.release updates).release embedding)
      ((heap.release updates).releaseStore (heap.releaseStore initial updates) embedding)
      status hidden cache hiddenBytes cacheBytes →
      wp «module» rest Q ((heap.release updates).releaseStore (heap.releaseStore initial updates) embedding) frame env) :
    wp «module» (finishUpdatesReleaseCode ++ finishAliasReleaseCode ++ finishEmbeddingReleaseCode ++ rest)
      Q initial frame env := by
  have hReadUpdates : frame.get 100 = some (.i64 updates.root) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.updatesOwner
  have hReadAlias : frame.get 101 = some (.i64 updates.root) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.updatesPtr
  have hReadEmbedding : frame.get 13 = some (.i64 embedding.root) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.embeddingOwner
  have hReadHidden : frame.get 121 = some (.i64 (statusRoot status hidden)) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.hiddenOwner
  have hReadCache : frame.get 124 = some (.i64 (statusRoot status cache)) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.cacheOwner
  simp only [List.append_assoc]
  unfold finishUpdatesReleaseCode
  apply finishRelease_spec env original initial before heap status hidden cache updates
    hiddenBytes cacheBytes updatesBytes frame 100
    [(13, embedding.root), (121, statusRoot status hidden), (124, statusRoot status cache)]
    hMemory hUpdates hUpdatesFresh hHiddenUpdates hCacheUpdates hState.values hReadUpdates
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact hReadEmbedding
    · exact hReadHidden
    · exact hReadCache
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact hUpdates.root_ne hTemporarySep
    · exact hUpdates.root_ne_status status hidden (fun h => regionsDisjoint_symm (hHiddenUpdates h))
    · exact hUpdates.root_ne_status status cache (fun h => regionsDisjoint_symm (hCacheUpdates h))
  intro hAfter
  unfold finishAliasReleaseCode
  apply PackedReleaseFilter.program_spec «module» env (heap.releaseStore initial updates) frame 101 updates.root
    [(100, updates.root), (13, embedding.root), (121, statusRoot status hidden), (124, statusRoot status cache)]
    [.localGet 101, .call 65] hState.values hReadAlias
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact hReadUpdates
    · exact hReadEmbedding
    · exact hReadHidden
    · exact hReadCache
  · intro hEnabled
    exact False.elim (hEnabled.2 (100, updates.root) (by simp) rfl)
  intro _
  have hRoot32 : updates.root.toNat ≤ 4294967296 := by
    have := hUpdates.buffer.addressBound
    omega
  have hAfterEmbedding := hEmbedding.released updates hUpdates.buffer.rootBound hRoot32
    (regionsDisjoint_symm hTemporarySep)
  unfold finishEmbeddingReleaseCode
  apply finishRelease_spec env original (heap.releaseStore initial updates) before (heap.release updates)
    status hidden cache embedding hiddenBytes cacheBytes embeddingBytes frame 13
    [(121, statusRoot status hidden), (124, statusRoot status cache)]
    hAfter hAfterEmbedding hEmbeddingFresh hHiddenEmbedding hCacheEmbedding hState.values hReadEmbedding
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact hReadHidden
    · exact hReadCache
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact hEmbedding.root_ne_status status hidden (fun h => regionsDisjoint_symm (hHiddenEmbedding h))
    · exact hEmbedding.root_ne_status status cache (fun h => regionsDisjoint_symm (hCacheEmbedding h))
  exact hNext

#print axioms cleanup_spec
end Project.Gpt2QuantizedCached.CachedHidden
