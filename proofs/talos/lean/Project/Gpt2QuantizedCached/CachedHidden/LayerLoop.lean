import Project.Gpt2QuantizedCached.CachedHidden.TraversalStep

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2.Quantized

set_option maxRecDepth 32768 in
theorem emitted_layerBody : layerBody =
    [.localGet 127, .localGet 128, .geUI64, .br_if 1] ++ (layerBody.drop 4).take 116 ++ [.br 0] := rfl

theorem layerLoop_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (embeddingNode : FreeNode) (weightsOwner weightsPtr cacheOwner cachePtr : UInt64)
    (weights cache : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hEmbedding : heap.OwnsPacked initial embeddingNode (embedding weights token position))
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hPosition : position < 128)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hWeightsSize : blocksOffset + 12 * blockBytes ≤ weights.size)
    (hResources : TraversalResources heap embeddingNode weights cache token position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : LayerFrame (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      embeddingNode.root embeddingNode.root 0 3072 0 0 0 frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result, TraversalState initial heap embeddingNode
      (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      weights cache token position 12 final result → wp «module» rest Q final result env) :
    wp «module» ((func58.drop 59).take 1 ++ rest) Q initial frame env := by
  let Inv : AssertionF Unit := fun current next => ∃ index, index ≤ 12 ∧
    TraversalState initial heap embeddingNode
      (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      weights cache token position index current next
  rw [emitted_layerLoop]
  simp only [List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := Inv) (μ := PackedGenerateLoop.measure 127 12)
  · exact ⟨0, by omega, traversalState_initial initial heap embeddingNode _ weights cache token position
      frame hHeap hEmbedding hState hPages⟩
  · rintro current next ⟨index, hIndex, hTraversal⟩
    have hCounter := hTraversal.state.counter_limit rfl
    have hValues := hTraversal.state.values
    have hEmpty : ({ next with values := [] } : Locals) = next := Frame.ext _ _ rfl rfl hValues.symm
    rw [emitted_layerBody]
    simp only [List.cons_append, List.nil_append,
      wp_localGet_cons, Frame.withValues_get, hCounter.1, hCounter.2, hValues,
      wp_geUI64_cons, wp_br_if_cons]
    by_cases hLast : index = 12
    · subst index
      have hGuard : UInt64.ofNat 12 ≥ (12 : UInt64) := by decide
      rw [ite_eq_left hGuard]
      simpa [hState.values, hEmpty] using
        hNext current next hTraversal
    · have hLt : index < 12 := by omega
      have hIndex64 : index < UInt64.size := by change index < 18446744073709551616; omega
      have hGuard : ¬(12 : UInt64) ≤ UInt64.ofNat index := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hIndex64]
        change ¬12 ≤ index
        omega
      simp only [ge_iff_le, hGuard, ite_false, hEmpty]
      apply traversalStep_spec env initial current heap embeddingNode weightsOwner weightsPtr cacheOwner cachePtr
        weights cache token position index next hEmbedding hWeights hCache hWeightsProtected hCacheProtected
        hPosition hLt hCacheSize hWeightsSize hResources hTraversal
      intro final result hResult
      simp only [wp_br_cons, List.take_zero, List.drop_zero, List.nil_append]
      have hResultEmpty : ({ result with values := [] } : Locals) = result :=
        Frame.ext _ _ rfl rfl hResult.state.values.symm
      constructor
      · simpa only [hResultEmpty] using (show Inv final result from ⟨index + 1, by omega, hResult⟩)
      · rw [hResultEmpty]
        simp only [PackedGenerateLoop.measure, (hResult.state.counter_limit rfl).1, hCounter.1,
          UInt64.toNat_ofNat_of_lt' hIndex64,
          UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by change index + 1 < 18446744073709551616; omega)]
        omega

#print axioms layerLoop_spec

end Project.Gpt2QuantizedCached.CachedHidden
