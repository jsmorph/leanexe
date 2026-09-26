import Project.Gpt2QuantizedCached.FP32Region
import Project.Gpt2CachedStep.LayerNorm.Spec

namespace Project.Gpt2QuantizedCached.LayerNorm
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open Project.Gpt2CachedStep.LayerNorm

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
    (hResources : Resources heap rows (initial.memoryCap Project.Gpt2CachedStep.«module» 0))
    (hPages : initial.mem.pages ≤ 65536) :
    let output := LeanExe.Models.Gpt2.layerNorm weights input scaleOffset biasOffset rows
    TerminatesWith env Project.Gpt2QuantizedCached.«module» 34 initial
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
        final.memoryCap Project.Gpt2CachedStep.«module» 0 = initial.memoryCap Project.Gpt2CachedStep.«module» 0) := by
  exact Project.FunctionRegion.terminatesWith FP32Region.shift 20
    (by simp [FP32Region.domain]) (Project.Gpt2CachedStep.LayerNorm.Spec.layerNorm_exact
      env initial heap weightsOwner inputOwner weightsPtr inputPtr weights input scaleOffset biasOffset rows hHeap hWeights hInput hWeightsProtected hInputProtected hInputSize hScaleSize hBiasSize hResources hPages)

#print axioms layerNorm_exact
end Project.Gpt2QuantizedCached.LayerNorm
