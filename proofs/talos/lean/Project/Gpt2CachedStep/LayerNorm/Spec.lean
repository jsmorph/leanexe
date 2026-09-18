import Project.Gpt2CachedStep.LayerNorm.Body

namespace Project.Gpt2CachedStep.LayerNorm.Spec
open Wasm Project.ProofKit PackedMemory Project.EulerRiemann.Execution

theorem layerNorm_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (scaleOffset biasOffset rows : Nat)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hInputSize : rows * 768 * 4 ≤ input.size)
    (hScaleSize : (scaleOffset + 768) * 4 ≤ weights.size)
    (hBiasSize : (biasOffset + 768) * 4 ≤ weights.size)
    (hResources : Resources heap rows (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536) :
    let output := LeanExe.Models.Gpt2.layerNorm weights input scaleOffset biasOffset rows
    TerminatesWith env «module» 20 initial
      [.i64 (UInt64.ofNat rows), .i64 (UInt64.ofNat biasOffset), .i64 (UInt64.ofNat scaleOffset),
       .i64 (UInt64.ofNat input.size), .i64 inputPtr, .i64 inputOwner,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr, .i64 weightsOwner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat output.size),
          .i64 (outputNode heap rows).root, .i64 (outputNode heap rows).root] ∧
        (finalHeap heap rows).At final ∧
        (finalHeap heap rows).OwnsPacked final (outputNode heap rows) output ∧
        heap.Frame initial (finalHeap heap rows) final ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap «module» 0 = initial.memoryCap «module» 0) := by
  dsimp only
  refine TerminatesWith.of_wp_entry_for (f := func20Def) rfl ?_
  change wp «module» func20 _ initial
    { params := parameters weightsOwner inputOwner weightsPtr inputPtr weights input scaleOffset biasOffset rows
      locals := List.replicate 74 (.i64 0) } env
  apply body_spec env initial heap weightsOwner inputOwner weightsPtr inputPtr weights input
    scaleOffset biasOffset rows _ hHeap hWeights hInput hWeightsProtected hInputProtected
    hInputSize hScaleSize hBiasSize hResources hPages rfl (by simp) rfl
    (I64Values.replicate _ _)
  intro final result hValues hFinalHeap hOutput hFrame hFinalPages hCapacity
  have hPost := And.intro hFinalHeap (And.intro hOutput (And.intro hFrame (And.intro hFinalPages hCapacity)))
  simpa [func20Def, Function.numParams, hValues, layerNorm_size, -UInt64.ofNat_mul] using hPost

#print axioms layerNorm_exact

end Project.Gpt2CachedStep.LayerNorm.Spec
