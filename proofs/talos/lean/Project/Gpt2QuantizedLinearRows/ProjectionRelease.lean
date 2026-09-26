import Project.Gpt2QuantizedLinearRows.ProjectionAllocate

namespace Project.Gpt2QuantizedLinearRows.Projection
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def releasedStore (heap : Heap) (initial : Store Unit) (valueNode scaleNode : FreeNode) : Store Unit :=
  (heap.release valueNode).releaseStore (heap.releaseStore initial valueNode) scaleNode

set_option maxRecDepth 32768 in
theorem releaseCode_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (valueNode scaleNode outputNode : FreeNode) (values scales output : ByteArray)
    (params : List Wasm.Value) (width outputWidth rows : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hValue : heap.OwnsPacked initial valueNode values)
    (hScale : heap.OwnsPacked initial scaleNode scales)
    (hOutput : heap.OwnsPacked initial outputNode output)
    (hValueScale : regionsDisjoint valueNode.region scaleNode.region)
    (hOutputValue : regionsDisjoint outputNode.region valueNode.region)
    (hOutputScale : regionsDisjoint outputNode.region scaleNode.region)
    (hParamsLength : params.length = 11)
    (hState : OutputState params valueNode.root scaleNode.root width outputWidth rows frame)
    (hReady : PackedGenerateLoop.Ready 29 72 73 (rows * outputWidth) (rows * outputWidth) outputNode.root frame)
    (hEmpty : frame.values = [])
    (Q : Assertion Unit)
    (hDone : ∀ result,
      ((heap.release valueNode).release scaleNode).At (releasedStore heap initial valueNode scaleNode) →
      ((heap.release valueNode).release scaleNode).OwnsPacked
        (releasedStore heap initial valueNode scaleNode) outputNode output →
      result.values = [.i64 (UInt64.ofNat (4 * (rows * outputWidth))), .i64 outputNode.root] →
      Q (.Fallthrough (releasedStore heap initial valueNode scaleNode) result)) :
    wp «module» (func8.drop 84) Q initial frame env := by
  rcases hState with ⟨hParams, hLocals, hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr,
    hValueSize, hScaleCopyOwner, hScalePtr, hScaleSize, hBytes, hTyped⟩
  have hOutputPtr : frame.locals[62]? = some (.i64 outputNode.root) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hReady.2.2.2.1
  have hValueNe : valueNode.root ≠ 0 := by
    intro h
    have := hValue.buffer.rootBound
    rw [h] at this
    contradiction
  have hScaleNe : scaleNode.root ≠ 0 := by
    intro h
    have := hScale.buffer.rootBound
    rw [h] at this
    contradiction
  have hValueOutput := (hOutput.root_ne hOutputValue).symm
  have hScaleOutput := (hOutput.root_ne hOutputScale).symm
  have hScaleValue := (hValue.root_ne hValueScale).symm
  have hScaleAfter := hScale.released valueNode hValue.buffer.rootBound
    (by have := hValue.buffer.addressBound; omega) (Or.symm hValueScale)
  have hOutputAfterValue := hOutput.released valueNode hValue.buffer.rootBound
    (by have := hValue.buffer.addressBound; omega) hOutputValue
  have hOutputFinal := hOutputAfterValue.released scaleNode hScale.buffer.rootBound
    (by have := hScale.buffer.addressBound; omega) hOutputScale
  simp only [func8, List.drop]
  wp_packed_frame [hParams, hParamsLength, hLocals, hEmpty, hOutputPtr, hBytes, hValueOwner]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simpa using hValueNe)]
  wp_packed_frame [hParams, hParamsLength, hLocals, hValueOwner]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simpa using hValueOutput)]
  wp_packed_frame [hParams, hParamsLength, hLocals, hValueOwner]
  refine wp_call_tw ((heap.releasePacked_exact env «module» 12 initial valueNode values
    (typeIdx := some 12) rfl rfl hHeap hValue).append_args rfl rfl rfl []) ?_
  rintro afterValue returned ⟨out, rfl, rfl, rfl, hHeapValue⟩
  wp_packed_frame [hParams, hParamsLength, hLocals, hScaleOwner, hValueOwner]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simpa using hScaleNe)]
  wp_packed_frame [hParams, hParamsLength, hLocals, hScaleOwner, hValueOwner]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simpa using hScaleValue)]
  wp_packed_frame [hParams, hParamsLength, hLocals, hScaleOwner, hValueOwner]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simpa using hScaleOutput)]
  wp_packed_frame [hParams, hParamsLength, hLocals, hScaleOwner, hValueOwner]
  refine wp_call_tw (((heap.release valueNode).releasePacked_exact env «module» 12
    (heap.releaseStore initial valueNode) scaleNode scales (typeIdx := some 12)
    rfl rfl hHeapValue hScaleAfter).append_args rfl rfl rfl []) ?_
  rintro final returned ⟨out, rfl, rfl, rfl, hHeapFinal⟩
  wp_packed_frame [hParams, hParamsLength, hLocals]
  exact hDone _ hHeapFinal hOutputFinal rfl

#print axioms releaseCode_spec

end Project.Gpt2QuantizedLinearRows.Projection
