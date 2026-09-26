import Project.Gpt2QuantizedCached.CachedBlock.Body

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock.Spec
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def sourceResultValues (output : HiddenResult) (hidden cache : UInt64) : List Value :=
  [.i64 (UInt64.ofNat output.cache.size), .i64 (if output.status = 0 then cache else 0),
   .i64 (if output.status = 0 then cache else 0), .i64 (UInt64.ofNat output.hidden.size),
   .i64 (if output.status = 0 then hidden else 0), .i64 (if output.status = 0 then hidden else 0),
   .i64 output.status]

theorem resultValues_source (weights input cache : ByteArray) (layer position : Nat)
    (hiddenRoot cacheRoot : UInt64) (hInput : input.size = 3072) :
    resultValues (tensors weights input cache layer position).accepted hiddenRoot cacheRoot =
      sourceResultValues (cachedBlock weights input cache layer position) hiddenRoot cacheRoot := by
  rw [cachedBlock_tensors]
  have hSizes := tensors_sizes weights input cache layer position hInput
  generalize ht : tensors weights input cache layer position = values at hSizes ⊢
  cases hAccepted : values.accepted <;>
    simp only [hAccepted, Bool.false_eq_true, ite_false, ite_true, sourceResultValues,
      resultValues, hSizes.hidden, Project.Gpt2CachedStep.CachedBlock.cacheUpdate_size,
      ByteArray.size_empty, reduceIte] <;> rfl

theorem Completion.sourceOutputs (weights input cache : ByteArray) (layer position : Nat)
    {heap after : Heap} {initial final : Store Unit} {hidden cacheNode : FreeNode}
    (h : Completion heap initial after final (tensors weights input cache layer position).accepted
      hidden cacheNode (tensors weights input cache layer position).hidden
      (Project.Gpt2CachedStep.CachedBlock.cacheUpdate (tensors weights input cache layer position).qkv))
    (hStatus : (cachedBlock weights input cache layer position).status = 0) :
    after.OwnsPacked final hidden (cachedBlock weights input cache layer position).hidden ∧
    after.OwnsPacked final cacheNode (cachedBlock weights input cache layer position).cache := by
  rw [cachedBlock_tensors] at hStatus ⊢
  generalize ht : tensors weights input cache layer position = values at h hStatus ⊢
  cases hAccepted : values.accepted
  · simp only [hAccepted, Bool.false_eq_true, ite_false] at hStatus
    contradiction
  · simpa only [hAccepted, ite_true] using h.outputs hAccepted

theorem cachedBlock_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr : UInt64)
    (weights input cache : ByteArray) (layer position : Nat)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hLayer : layer < 12) (hPosition : position < 128)
    (hExtent : blocksOffset + layer * blockBytes + blockBytes ≤ weights.size)
    (hInputSize : input.size = 3072) (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hResources : Resources heap position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env «module» 54 initial
      [.i64 (UInt64.ofNat position), .i64 (UInt64.ofNat layer),
       .i64 (UInt64.ofNat cache.size), .i64 cachePtr, .i64 cacheOwner,
       .i64 (UInt64.ofNat input.size), .i64 inputPtr, .i64 inputOwner,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr, .i64 weightsOwner]
      (fun final returned =>
        returned = sourceResultValues (cachedBlock weights input cache layer position)
          (hiddenNode heap position).root (cacheNode heap position).root ∧
        Completion heap initial (executionHeap heap position (tensors weights input cache layer position)) final
          (tensors weights input cache layer position).accepted
          (hiddenNode heap position) (cacheNode heap position)
          (tensors weights input cache layer position).hidden
          (Project.Gpt2CachedStep.CachedBlock.cacheUpdate (tensors weights input cache layer position).qkv)) := by
  refine TerminatesWith.of_wp_entry_for (f := func54Def) rfl ?_
  change wp «module» func54 _ initial
    { params := parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position
      locals := List.replicate 193 (.i64 0) } env
  apply body_spec env initial heap weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    weights input cache layer position _ hHeap hWeights hInput hCache hWeightsProtected hInputProtected
    hCacheProtected hLayer hPosition hExtent hInputSize hCacheSize hResources hPages
    rfl (List.length_replicate ..) rfl (I64Values.replicate _ _)
  intro final result hValues hOutput
  rw [resultValues_source weights input cache layer position _ _ hInputSize] at hValues
  simpa only [func54Def, Function.numParams, hValues, sourceResultValues, List.length_cons,
    List.length_nil, Nat.reduceAdd, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, List.append_nil, true_and] using hOutput

#print axioms resultValues_source
#print axioms Completion.sourceOutputs
#print axioms cachedBlock_exact
end Project.Gpt2QuantizedCached.CachedBlock.Spec
