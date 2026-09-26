import Project.Gpt2QuantizedCached.CachedHidden.TraversalTransfer

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem traversalStep_spec (env : HostEnv Unit) (initial current : Store Unit) (heap : Heap)
    (embeddingNode : FreeNode) (weightsOwner weightsPtr cacheOwner cachePtr : UInt64)
    (weights cache : ByteArray) (token : UInt32) (position index : Nat) (frame : Locals)
    (hEmbedding : heap.OwnsPacked initial embeddingNode (embedding weights token position))
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hPosition : position < 128) (hIndex : index < 12)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hWeightsSize : blocksOffset + 12 * blockBytes ≤ weights.size)
    (hResources : TraversalResources heap embeddingNode weights cache token position (initial.memoryCap «module» 0))
    (hState : TraversalState initial heap embeddingNode
      (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      weights cache token position index current frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result, TraversalState initial heap embeddingNode
      (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      weights cache token position (index + 1) final result → wp «module» rest Q final result env) :
    wp «module» ((layerBody.drop 4).take 137 ++ rest) Q current frame env := by
  by_cases hZero : (layerPrefix weights cache token position index).2.2 = 0
  · have hLayerWeights : blocksOffset + index * blockBytes + blockBytes ≤ weights.size := by
      apply Nat.le_trans _ hWeightsSize
      rw [Nat.add_assoc, ← Nat.succ_mul]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right blockBytes (by omega)) blocksOffset
    have hLayerResources : LayerResources
        (traversal heap embeddingNode weights cache token position index).heap position
        (CachedBlock.tensors weights (layerPrefix weights cache token position index).1 cache index position)
        (layerPrefix weights cache token position index).2.1
        (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position)
        (current.memoryCap «module» 0) := by
      rw [hState.capacity]
      exact hResources.layer index hIndex hZero
    have hSizes := (layerPrefix_valid weights cache token position index).success hZero
    have hInputZero : index = 0 →
        (traversal heap embeddingNode weights cache token position index).hidden.root = embeddingNode.root := by
      rintro rfl
      rfl
    have hUpdatesZero : index = 0 →
        (traversal heap embeddingNode weights cache token position index).updates.root = 0 := by
      rintro rfl
      rfl
    apply activeStep_spec env initial current heap (traversal heap embeddingNode weights cache token position index).heap
      weightsOwner weightsPtr cacheOwner cachePtr embeddingNode
      (traversal heap embeddingNode weights cache token position index).hidden
      (traversal heap embeddingNode weights cache token position index).updates
      (embedding weights token position) weights (layerPrefix weights cache token position index).1 cache
      (layerPrefix weights cache token position index).2.1 token position index frame
      hState.heapAt hState.preserved hState.capacity hEmbedding
      (hState.preserved.packed hWeightsProtected hWeights) (hState.preserved.packed hCacheProtected hCache)
      (hState.hidden.owned hZero) hState.updates hState.updatesOwned
      (hState.preserved.protects _ _ hWeightsProtected) (hState.preserved.protects _ _ hCacheProtected)
      hState.updatesProtected (fun h => hState.hiddenFresh h hZero) hState.updatesFresh
      hInputZero hUpdatesZero (fun h => hState.separated h hZero) hIndex hPosition
      hSizes.1 hSizes.2 hCacheSize hLayerWeights hLayerResources hState.pages
      (by simpa only [statusRoot, hZero, ite_true] using hState.state)
    intro final result
    dsimp only
    intro hResult hOutput
    apply hNext final result
    exact traversalState_active initial final heap embeddingNode _ weights cache token position index result
      hZero hResult hOutput
  · have hNonzero : index ≠ 0 := by
      intro hIndexZero
      subst index
      exact hZero rfl
    apply inactiveStep_spec env current _ embeddingNode.root
      (statusRoot (layerPrefix weights cache token position index).2.2
        (traversal heap embeddingNode weights cache token position index).hidden)
      (traversal heap embeddingNode weights cache token position index).updates.root
      (layerPrefix weights cache token position index).1.size
      (layerPrefix weights cache token position index).2.1.size
      (layerPrefix weights cache token position index).2.2 index frame rfl hIndex hZero hState.state
    intro result hResult
    apply hNext current result
    have hPrefix := layerPrefix_succ weights cache token position index
    rw [layerStep_nonzero _ _ _ _ _ hZero] at hPrefix
    have hTraversal : traversal heap embeddingNode weights cache token position (index + 1) =
        traversal heap embeddingNode weights cache token position index := by
      simp only [traversal, traversalStep, hZero, ite_false]
    constructor
    · simpa only [hPrefix, hTraversal] using hResult
    · simpa only [hTraversal] using hState.heapAt
    · simpa only [hPrefix, hTraversal] using hState.hidden
    · simpa only [hPrefix, hTraversal] using hState.updates
    · simpa only [hPrefix, hTraversal] using hState.updatesProtected
    · intro _
      simpa only [hPrefix, hTraversal] using hState.updatesOwned hNonzero
    · simpa only [hTraversal] using hState.preserved
    · intro _
      simpa only [hPrefix, hTraversal] using hState.hiddenFresh hNonzero
    · intro _
      simpa only [hTraversal] using hState.updatesFresh hNonzero
    · intro _
      simpa only [hPrefix, hTraversal] using hState.separated hNonzero
    · exact hState.pages
    · exact hState.capacity

#print axioms traversalStep_spec
end Project.Gpt2QuantizedCached.CachedHidden
