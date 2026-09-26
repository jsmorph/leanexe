import Project.Gpt2CachedStep.Vocabulary.FrozenBody

namespace Project.Gpt2CachedStep.Frozen.Vocabulary.Spec
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2

theorem vocabularyHead_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hWeightsSize : 50257 * 768 * 4 ≤ weights.size) (hInputSize : 3072 ≤ input.size)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hBump : takeFirstFitFrom 0 outputNeed heap.nodes = none →
      heap.top.toNat + 48 + outputNeed.toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top outputNeed ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env «module» 37 initial
      [.i64 (UInt64.ofNat input.size), .i64 inputPtr, .i64 inputOwner,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr, .i64 weightsOwner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat (vocabularyHead weights input).size),
          .i64 (allocatedRoot heap.top outputNeed heap.nodes), .i64 (allocatedRoot heap.top outputNeed heap.nodes)] ∧
        heap.PackedOutput initial final outputNeed (vocabularyHead weights input)) := by
  refine TerminatesWith.of_wp_entry_for (f := func37Def) rfl ?_
  change wp «module» func37 _ initial
    { params := parameters weightsOwner inputOwner weightsPtr inputPtr weights input,
      locals := List.replicate 35 (.i64 0) } env
  apply body_spec env initial heap weightsOwner inputOwner weightsPtr inputPtr weights input _
    hHeap hWeights hInput hWeightsSize hInputSize hWeightsProtected hInputProtected hBump hPages
    rfl (List.length_replicate ..) rfl (I64Values.replicate _ _)
  intro final result hValues hOutput
  simpa [func37Def, Function.numParams, hValues, vocabularyHead_size] using hOutput

#print axioms vocabularyHead_exact

end Project.Gpt2CachedStep.Frozen.Vocabulary.Spec
