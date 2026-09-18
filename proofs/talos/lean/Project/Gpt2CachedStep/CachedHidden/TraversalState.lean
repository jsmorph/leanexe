import Project.Gpt2CachedStep.CachedHidden.LayerStep
import Project.Gpt2CachedStep.CachedHidden.Traversal

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2

structure TraversalState (initial : Store Unit) (heap : Heap) (embeddingNode : FreeNode)
    (params : List Value) (weights cache : ByteArray) (token : UInt32) (position index : Nat)
    (current : Store Unit) (frame : Locals) : Prop where
  state : LayerState params embeddingNode.root (traversal heap embeddingNode position index).hidden.root
    (traversal heap embeddingNode position index).updates.root index
    (layerPrefix weights cache token position index).2.size frame
  heapAt : (traversal heap embeddingNode position index).heap.At current
  hidden : (traversal heap embeddingNode position index).heap.OwnsPacked current
    (traversal heap embeddingNode position index).hidden (layerPrefix weights cache token position index).1
  updates : ByteArrayAt current.mem (traversal heap embeddingNode position index).updates.root.toNat
    (layerPrefix weights cache token position index).2
  updatesProtected : (traversal heap embeddingNode position index).heap.Protects
    (traversal heap embeddingNode position index).updates.root.toNat
    ((traversal heap embeddingNode position index).updates.root.toNat + (layerPrefix weights cache token position index).2.size)
  updatesOwned : index ≠ 0 → (traversal heap embeddingNode position index).heap.OwnsPacked current
    (traversal heap embeddingNode position index).updates (layerPrefix weights cache token position index).2
  preserved : heap.Frame initial (traversal heap embeddingNode position index).heap current
  hiddenFresh : index ≠ 0 → heap.FreshNode (traversal heap embeddingNode position index).hidden
  updatesFresh : index ≠ 0 → heap.FreshNode (traversal heap embeddingNode position index).updates
  separated : index ≠ 0 → regionsDisjoint (traversal heap embeddingNode position index).hidden.region
    (traversal heap embeddingNode position index).updates.region
  pages : current.mem.pages ≤ 65536
  capacity : current.memoryCap «module» 0 = initial.memoryCap «module» 0

theorem LayerState.counter_limit {params : List Value} {embeddingPtr inputPtr updatesPtr : UInt64}
    {index updatesSize : Nat} {frame : Locals} (h : LayerState params embeddingPtr inputPtr updatesPtr index updatesSize frame)
    (hParams : params.length = 8) :
    frame.get 103 = some (.i64 (UInt64.ofNat index)) ∧ frame.get 104 = some (.i64 12) := by
  rcases h with ⟨hParameters, hLocals, _, _, _, _, _, _, _, _, _, _, _, hCounter, hLimit, _, _⟩
  simp only [Locals.get, hParameters, hParams, hLocals, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, ite_false, ite_true,
    hCounter, hLimit, and_self]

theorem traversalState_initial (initial : Store Unit) (heap : Heap) (embeddingNode : FreeNode)
    (params : List Value) (weights cache : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hEmbedding : heap.OwnsPacked initial embeddingNode (embedding weights token position))
    (hState : LayerState params embeddingNode.root embeddingNode.root 0 0 0 frame)
    (hPages : initial.mem.pages ≤ 65536) :
    TraversalState initial heap embeddingNode params weights cache token position 0 initial frame := by
  refine ⟨hState, hHeap, hEmbedding, ?_, ?_, ?_, Heap.Frame.refl .., ?_, ?_, ?_, hPages, rfl⟩
  · simp [traversal, layerPrefix_zero, ByteArrayAt]
  · exact ⟨Nat.zero_le _, fun _ _ => Or.inl (Nat.zero_le _)⟩
  all_goals intro h; exact False.elim (h rfl)

theorem traversalStep_spec (env : HostEnv Unit) (initial current : Store Unit) (heap : Heap)
    (embeddingNode : FreeNode) (weightsOwner weightsPtr cacheOwner cachePtr : UInt64)
    (weights cache : ByteArray) (token : UInt32) (position index : Nat) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hPosition : position < 128) (hIndex : index < 12)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hWeightsSize : (blocksOffset + 12 * blockWords) * 4 ≤ weights.size)
    (hResources : TraversalResources heap embeddingNode position (initial.memoryCap «module» 0))
    (hState : TraversalState initial heap embeddingNode
      (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      weights cache token position index current frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result, TraversalState initial heap embeddingNode
      (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      weights cache token position (index + 1) final result → wp «module» rest Q final result env) :
    wp «module» ((layerBody.drop 4).take 217 ++ rest) Q current frame env := by
  have hLayerWeights : (blocksOffset + index * blockWords + blockWords) * 4 ≤ weights.size := by
    apply Nat.le_trans _ hWeightsSize
    apply Nat.mul_le_mul_right 4
    rw [Nat.add_assoc, ← Nat.succ_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right blockWords (by omega)) blocksOffset
  have hLayerResources : LayerResources (traversal heap embeddingNode position index).heap position index
      (current.memoryCap «module» 0) := by
    rw [hState.capacity]
    exact hResources.layer index hIndex
  have hSize : (layerPrefix weights cache token position index).2.size + 6144 =
      (layerPrefix weights cache token position (index + 1)).2.size := by
    rw [(layerPrefix_sizes weights cache token position index).2,
      (layerPrefix_sizes weights cache token position (index + 1)).2]
    omega
  apply layerStep_spec env initial current heap (traversal heap embeddingNode position index).heap
    weightsOwner weightsPtr cacheOwner cachePtr embeddingNode.root
    (traversal heap embeddingNode position index).hidden (traversal heap embeddingNode position index).updates
    weights (layerPrefix weights cache token position index).1 cache (layerPrefix weights cache token position index).2
    token position index frame hState.heapAt hState.preserved
    (hState.preserved.packed hWeightsProtected hWeights) (hState.preserved.packed hCacheProtected hCache)
    hState.hidden hState.updates hState.updatesOwned
    (hState.preserved.protects _ _ hWeightsProtected) (hState.preserved.protects _ _ hCacheProtected)
    hState.updatesProtected hState.hiddenFresh hState.updatesFresh hState.separated hIndex hPosition
    (layerPrefix_sizes weights cache token position index).1 (layerPrefix_sizes weights cache token position index).2
    hCacheSize hLayerWeights hLayerResources hState.pages hState.state
  intro final result hResult hHeap hHidden hUpdates hPreserved hHiddenFresh hUpdatesFresh hSeparated hPages hCapacity
  apply hNext final result
  refine ⟨?_, hHeap, ?_, ?_, ?_, ?_, hPreserved, fun _ => hHiddenFresh, fun _ => hUpdatesFresh,
    fun _ => hSeparated, hPages, hCapacity.trans hState.capacity⟩
  · simpa only [traversal, traversalStep, hSize] using hResult
  · simpa only [traversal, traversalStep, layerPrefix_succ, layerStep] using hHidden
  · simpa only [traversal, traversalStep, layerPrefix_succ, layerStep] using hUpdates.buffer.values
  · simpa only [traversal, traversalStep, layerPrefix_succ, layerStep] using hUpdates.payload_protects
  · intro _
    simpa only [traversal, traversalStep, layerPrefix_succ, layerStep] using hUpdates

#print axioms traversalState_initial
#print axioms traversalStep_spec

end Project.Gpt2CachedStep.CachedHidden
