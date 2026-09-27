import Project.Gpt2QuantizedLinearRows.ProjectionInput
import Project.Gpt2QuantizedLinearRows.ProjectionRelease

namespace Project.Gpt2QuantizedLinearRows.Projection
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution LeanExe.Models.Gpt2.Quantized

def outputNode (heap : Heap) (width outputWidth rows : Nat) : FreeNode :=
  let next := QuantizeRows.outputHeap heap width rows
  allocatedNode next.top (need outputWidth rows) next.nodes

def outputHeap (heap : Heap) (width outputWidth rows : Nat) : Heap :=
  (((QuantizeRows.outputHeap heap width rows).allocate (need outputWidth rows)).release
    (QuantizeRows.valueNode heap width rows)).release (QuantizeRows.scaleNode heap rows)

theorem outputHeap_counts (heap : Heap) (width outputWidth rows : Nat) :
    (outputHeap heap width outputWidth rows).allocations = heap.allocations + 3 ∧
    (outputHeap heap width outputWidth rows).retains = heap.retains ∧
    (outputHeap heap width outputWidth rows).releases = heap.releases + 2 ∧
    (outputHeap heap width outputWidth rows).frees = heap.frees + 2 := by
  simp [outputHeap, QuantizeRows.outputHeap, Heap.allocate, Heap.release, UInt64.add_assoc]

structure Output (heap : Heap) (initial final : Store Unit) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool) : Prop where
  heapAt : (outputHeap heap width outputWidth rows).At final
  owned : (outputHeap heap width outputWidth rows).OwnsPacked final (outputNode heap width outputWidth rows)
    (linearRows weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias)
  frame : heap.Frame initial (outputHeap heap width outputWidth rows) final
  pages : final.mem.pages ≤ 65536
  memoryCap : ∀ (module_ : Wasm.Module) (index : Nat),
    final.memoryCap module_ index = initial.memoryCap module_ index

set_option maxRecDepth 32768 in
theorem entry_parts : func8 = func8.take 34 ++ sizeCode ++ (func8.drop 52).take 32 ++ func8.drop 84 := rfl

end Project.Gpt2QuantizedLinearRows.Projection

namespace Project.Gpt2QuantizedLinearRows.Spec
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution Projection

set_option maxRecDepth 32768 in
theorem linearRows_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hWeightSize : weightOffset + width * outputWidth ≤ weights.size)
    (hScaleSize : scaleOffset + outputWidth * 4 ≤ weights.size)
    (hBiasSize : withBias = true → biasOffset + outputWidth * 4 ≤ weights.size)
    (hInputSize : rows * width * 4 ≤ input.size) (hWidth : 0 < width)
    (hWeightProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hScaleCount : 4 * rows ≤ 2^32) (hOutputCount : 4 * (rows * outputWidth) ≤ 2^32)
    (hScaleBump : takeFirstFitFrom 0 (QuantizeRows.scaleNeed rows) heap.nodes = none →
      heap.top.toNat + 48 + (QuantizeRows.scaleNeed rows).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (QuantizeRows.scaleNeed rows) ≤ initial.memoryCap «module» 0)
    (hByteBump : let next := heap.allocate (QuantizeRows.scaleNeed rows)
      takeFirstFitFrom 0 (QuantizeRows.byteNeed width rows) next.nodes = none →
        next.top.toNat + 48 + (QuantizeRows.byteNeed width rows).toNat < 4294967296 ∧
        FixedArrayBump.requiredPages next.top (QuantizeRows.byteNeed width rows) ≤ initial.memoryCap «module» 0)
    (hOutputBump : let next := QuantizeRows.outputHeap heap width rows
      takeFirstFitFrom 0 (need outputWidth rows) next.nodes = none →
        next.top.toNat + 48 + (need outputWidth rows).toNat < 4294967296 ∧
        FixedArrayBump.requiredPages next.top (need outputWidth rows) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env «module» 8 initial
      (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias).reverse
      (fun final values =>
        values = [.i64 (UInt64.ofNat (4 * (rows * outputWidth))), .i64 (outputNode heap width outputWidth rows).root] ∧
        Output heap initial final weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias) := by
  let entry : Locals :=
    { params := parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias,
      locals := List.replicate 73 (.i64 0), values := [] }
  refine TerminatesWith.of_wp_entry_for (f := func8Def) rfl ?_
  change wp «module» func8 _ initial entry env
  rw [entry_parts, List.append_assoc, List.append_assoc]
  apply inputCode_spec env initial heap weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
    width outputWidth rows withBias entry hHeap hInput hInputSize hInputProtected hScaleCount
    hScaleBump hByteBump hPages rfl (by simp [entry]) rfl
  intro quantizedStore hQuantized
  let next := QuantizeRows.outputHeap heap width rows
  let valueNode := QuantizeRows.valueNode heap width rows
  let scaleNode := QuantizeRows.scaleNode heap rows
  let quantizedFrame := inputFrame entry inputPtr input width rows valueNode.root scaleNode.root
  have hBump : takeFirstFitFrom 0 (need outputWidth rows) next.nodes = none →
      next.top.toNat + 48 + (need outputWidth rows).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages next.top (need outputWidth rows) ≤ quantizedStore.memoryCap «module» 0 := by
    intro h
    exact ⟨(hOutputBump h).1, by rw [hQuantized.memoryCap]; exact (hOutputBump h).2⟩
  apply sizeCode_spec env quantizedStore quantizedFrame outputWidth rows
    rfl (by simp [quantizedFrame, inputFrame, entry]) rfl rfl rfl hOutputCount
  apply allocatedOutput_spec env quantizedStore next weightsPtr inputPtr valueNode.root scaleNode.root
    weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias
    (sizeFrame quantizedFrame outputWidth rows) hQuantized.heapAt
    (hQuantized.frame.packed hWeightProtected hWeights)
    hQuantized.values.buffer.values hQuantized.scales.buffer.values hWeightSize hScaleSize hBiasSize hWidth
    (hQuantized.frame.protects _ _ hWeightProtected)
    (by simpa only [quantized_values_size] using hQuantized.values.payload_protects)
    (by simpa only [quantized_scales_size] using hQuantized.scales.payload_protects)
    hOutputCount hBump hQuantized.pages
    (input_size_state entry inputPtr input width outputWidth rows valueNode.root scaleNode.root
      (by simp [entry]) (I64Values.replicate 73 0)) rfl
    (by simp [sizeFrame, quantizedFrame, inputFrame, entry, parameters, Locals.get])
  intro outputStore outputFrame hReady hState hOutput
  have hValuesOwned := hOutput.frame.ownsPacked hOutput.heapAt hQuantized.values
  have hScalesOwned := hOutput.frame.ownsPacked hOutput.heapAt hQuantized.scales
  have hValueSep := hQuantized.values.allocation_disjoint (need outputWidth rows) (fun h => (hOutputBump h).1.le)
  have hScaleSep := hQuantized.scales.allocation_disjoint (need outputWidth rows) (fun h => (hOutputBump h).1.le)
  have hBaseFrame := hQuantized.frame.trans hOutput.frame
  have hValueFrame := hBaseFrame.released valueNode hValuesOwned.buffer.rootBound
    (by dsimp only [valueNode]; have := hValuesOwned.buffer.addressBound; omega) (by
      intro lo hi hProtected
      have hScaleFrame := heap.frame_allocatePacked initial (QuantizeRows.scaleNeed rows) hHeap
        (fun h => (hScaleBump h).1.le)
      exact (hScaleFrame.protects lo hi hProtected).allocated_disjoint (QuantizeRows.byteNeed width rows)
        (fun h => (hByteBump h).1.le))
  have hFinalFrame := hValueFrame.released scaleNode hScalesOwned.buffer.rootBound
    (by dsimp only [scaleNode]; have := hScalesOwned.buffer.addressBound; omega) (by
      intro lo hi hProtected
      exact hProtected.allocated_disjoint (QuantizeRows.scaleNeed rows) (fun h => (hScaleBump h).1.le))
  apply releaseCode_spec env outputStore (next.allocate (need outputWidth rows))
    valueNode scaleNode (outputNode heap width outputWidth rows) _ _ _ _ width outputWidth rows outputFrame
    hOutput.heapAt hValuesOwned hScalesOwned hOutput.owned (Or.symm hQuantized.separated)
    (Or.symm hValueSep) (Or.symm hScaleSep) rfl hState hReady hReady.1
  intro result hFinalHeap hFinalOwner hResult
  have hFinalOutput : Output heap initial
      (Projection.releasedStore (next.allocate (need outputWidth rows)) outputStore valueNode scaleNode)
      weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias := by
    refine ⟨hFinalHeap, hFinalOwner, hFinalFrame, ?_, ?_⟩
    · simpa only [Projection.releasedStore, Heap.releaseStore,
        Project.EulerRiemann.Execution.releasedStore_pages] using hOutput.pages
    · intro module_ index
      simp only [Projection.releasedStore, Heap.releaseStore,
        Project.EulerRiemann.Execution.releasedStore_memoryCap]
      exact (hOutput.memoryCap module_ index).trans (hQuantized.memoryCap module_ index)
  simpa [func8Def, Function.numParams, parameters, hResult] using hFinalOutput

#print axioms linearRows_exact

end Project.Gpt2QuantizedLinearRows.Spec
