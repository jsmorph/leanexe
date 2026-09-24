import Project.Gpt2CachedStep.LayerNorm.FrozenResources

namespace Project.Gpt2CachedStep.Frozen.LayerNorm
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution

set_option maxRecDepth 32768 in
theorem body_shape : func20 = func20.take 49 ++ (func20.drop 49).take 49 ++
    (func20.drop 98).take 58 ++ func20.drop 156 := rfl

theorem body_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (scaleOffset biasOffset rows : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hInputSize : rows * 768 * 4 ≤ input.size)
    (hScaleSize : (scaleOffset + 768) * 4 ≤ weights.size)
    (hBiasSize : (biasOffset + 768) * 4 ≤ weights.size)
    (hResources : Resources heap rows (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner weightsPtr inputPtr weights input scaleOffset biasOffset rows)
    (hLocals : frame.locals.length = 74) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit)
    (hNext : ∀ final result,
      result.values = [.i64 (UInt64.ofNat (4 * (rows * 768))),
        .i64 (outputNode heap rows).root, .i64 (outputNode heap rows).root] →
      (finalHeap heap rows).At final →
      (finalHeap heap rows).OwnsPacked final (outputNode heap rows)
        (LeanExe.Models.Gpt2.layerNorm weights input scaleOffset biasOffset rows) →
      heap.Frame initial (finalHeap heap rows) final →
      final.mem.pages ≤ 65536 →
      final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      Q (.Fallthrough final result)) :
    wp «module» func20 Q initial frame env := by
  have hCount : 4 * (rows * 768) ≤ 2^32 := by have := hInput.1; omega
  have hTempCount : 4 * rows ≤ 2^32 := by omega
  rw [body_shape]
  simp only [List.append_assoc]
  apply means_spec env initial heap weightsOwner inputOwner weightsPtr inputPtr weights input
    scaleOffset biasOffset rows frame hHeap hInput hInputSize hInputProtected hTempCount
    hResources.means hPages hParams hLocals hValues hTyped
  intro first firstFrame hFirstState hFirst
  have hInputFirst := hFirst.frame.packed hInputProtected hInput
  have hInputProtectedFirst := hFirst.frame.protects _ _ hInputProtected
  have hInverseBump : AllocationFits (meansHeap heap rows) (temporaryNeed rows)
      (first.memoryCap «module» 0) := by rw [hFirst.memoryCap]; exact hResources.inverses
  have hMeanInverse := hFirst.owned.allocation_disjoint (temporaryNeed rows)
    (fun h => (hInverseBump h).1.le)
  apply inverses_spec env first (meansHeap heap rows) weightsOwner inputOwner weightsPtr inputPtr
    (meansNode heap rows).root weights input scaleOffset biasOffset rows firstFrame
    hFirst.heapAt hInputFirst hInputSize hInputProtectedFirst hFirst.owned.buffer.values
    hFirst.owned.payload_protects hTempCount hInverseBump hFirst.pages hFirstState
  intro second secondFrame hSecondState hSecond
  have hFrameSecond := hFirst.frame.trans hSecond.frame
  have hMeansSecond := hSecond.frame.ownsPacked hSecond.heapAt hFirst.owned
  have hOutputBump : AllocationFits (inversesHeap heap rows) (outputNeed rows)
      (second.memoryCap «module» 0) := by
    rw [hSecond.memoryCap, hFirst.memoryCap]
    exact hResources.output
  have hMeanOutput := hMeansSecond.allocation_disjoint (outputNeed rows)
    (fun h => (hOutputBump h).1.le)
  have hInverseOutput := hSecond.owned.allocation_disjoint (outputNeed rows)
    (fun h => (hOutputBump h).1.le)
  apply output_spec env second (inversesHeap heap rows) weightsOwner inputOwner weightsPtr inputPtr
    (meansNode heap rows).root (inversesNode heap rows).root weights input scaleOffset biasOffset rows secondFrame
    hSecond.heapAt (hFrameSecond.packed hWeightsProtected hWeights)
    (hFrameSecond.protects _ _ hWeightsProtected) hScaleSize hBiasSize
    (hFrameSecond.packed hInputProtected hInput) hInputSize (hFrameSecond.protects _ _ hInputProtected)
    hMeansSecond.buffer.values hMeansSecond.payload_protects hSecond.owned.buffer.values
    hSecond.owned.payload_protects hCount hOutputBump hSecond.pages hSecondState
  intro third thirdFrame hThirdState hThird
  have hFrameThird := hFrameSecond.trans hThird.frame
  have hMeansThird := hThird.frame.ownsPacked hThird.heapAt hMeansSecond
  have hInversesThird := hThird.frame.ownsPacked hThird.heapAt hSecond.owned
  have hMeanRoot := hMeansThird.buffer.rootBound
  have hMean32 : (meansNode heap rows).root.toNat ≤ 4294967296 := by
    have := hMeansThird.buffer.addressBound
    change (meansNode heap rows).root.toNat + (meansNode heap rows).capacity.toNat < 4294967296 at this
    omega
  have hInverseRoot := hInversesThird.buffer.rootBound
  have hInverse32 : (inversesNode heap rows).root.toNat ≤ 4294967296 := by
    have := hInversesThird.buffer.addressBound
    change (inversesNode heap rows).root.toNat + (inversesNode heap rows).capacity.toNat < 4294967296 at this
    omega
  have hFrameInverse := hFrameThird.released (inversesNode heap rows) hInverseRoot hInverse32
    (fun lo hi h => (hFirst.frame.protects lo hi h).allocated_disjoint (temporaryNeed rows)
      (fun h => (hResources.inverses h).1.le))
  have hFrameFinal := hFrameInverse.released (meansNode heap rows) hMeanRoot hMean32
    (fun _ _ h => h.allocated_disjoint (temporaryNeed rows) (fun h => (hResources.means h).1.le))
  rw [← List.append_nil (func20.drop 156)]
  apply cleanup_spec env third (outputHeap heap rows) thirdFrame _ (meansNode heap rows)
    (inversesNode heap rows) (outputNode heap rows) (means input rows) (inverses input rows)
    (LeanExe.Models.Gpt2.layerNorm weights input scaleOffset biasOffset rows) rows rfl hThird.heapAt
    hMeansThird hInversesThird hThird.owned hMeanInverse hMeanOutput hInverseOutput hThirdState
  rintro final result rfl hFinalHeap hFinalOutput hFinalValues
  simp only [wp_nil]
  apply hNext _ result hFinalValues hFinalHeap hFinalOutput hFrameFinal hThird.pages
  exact (hThird.memoryCap «module» 0).trans ((hSecond.memoryCap «module» 0).trans (hFirst.memoryCap «module» 0))

#print axioms body_spec

end Project.Gpt2CachedStep.Frozen.LayerNorm
