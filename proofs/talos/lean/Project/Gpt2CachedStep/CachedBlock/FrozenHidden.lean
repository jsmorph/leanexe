import Project.Gpt2CachedStep.CachedBlock.FrozenResidual

namespace Project.Gpt2CachedStep.Frozen.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def hiddenCode : Wasm.Program :=
  [.localGet 84, .localSet 145, .localGet 85, .localSet 146, .localGet 86, .localSet 147,
   .localGet 142, .localSet 148, .localGet 143, .localSet 149, .localGet 144, .localSet 150,
   .localGet 145, .localGet 146, .localGet 147, .localGet 148, .localGet 149, .localGet 150,
   .call 30, .localSet 153, .localSet 152, .localSet 151,
   .localGet 151, .localSet 161, .localGet 152, .localSet 162, .localGet 153, .localSet 163]

set_option maxRecDepth 32768 in
theorem emitted_hidden : (func33.drop 456).take 28 = hiddenCode := rfl

theorem hidden_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (residualPtr projected2Ptr : UInt64) (residual projected2 : ByteArray) (frame : Locals)
    (hHeap : heap.At initial)
    (hResidual : ByteArrayAt initial.mem residualPtr.toNat residual)
    (hProjected2 : ByteArrayAt initial.mem projected2Ptr.toNat projected2)
    (hResidualProtected : heap.Protects residualPtr.toNat (residualPtr.toNat + residual.size))
    (hProjected2Protected : heap.Protects projected2Ptr.toNat (projected2Ptr.toNat + projected2.size))
    (hResidualSize : residual.size = 3072) (hProjected2Size : projected2.size = 3072)
    (hResources : LayerNorm.AllocationFits heap projectionNeed (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = params) (hParamsLength : params.length = 11)
    (hLocals : frame.locals.length = 164) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (hResidualOwner : frame.locals[73]? = some (.i64 residualPtr))
    (hResidualPtr : frame.locals[74]? = some (.i64 residualPtr))
    (hResidualBytes : frame.locals[75]? = some (.i64 3072))
    (hProjected2Owner : frame.locals[131]? = some (.i64 projected2Ptr))
    (hProjected2Ptr : frame.locals[132]? = some (.i64 projected2Ptr))
    (hProjected2Bytes : frame.locals[133]? = some (.i64 3072))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState params (frame.locals.take 134) 134 140 150
        (allocatedNode heap.top projectionNeed heap.nodes).root 3072 result →
      (heap.allocate projectionNeed).At final →
      (heap.allocate projectionNeed).OwnsPacked final (allocatedNode heap.top projectionNeed heap.nodes)
        (addRows residual projected2) →
      heap.Frame initial (heap.allocate projectionNeed) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((func33.drop 456).take 28 ++ rest) Q initial frame env := by
  have hNeed : AddRows.need residual = projectionNeed := by rw [AddRows.need, hResidualSize]; rfl
  have hSize : (addRows residual projected2).size = 3072 := by
    rw [addRows, PackedSource.generate_size, hResidualSize]
  have hBump : LayerNorm.AllocationFits heap (AddRows.need residual) (initial.memoryCap «module» 0) := by
    rw [hNeed]
    exact hResources
  have hCall := AddRows.Spec.addRows_exact env initial heap residualPtr projected2Ptr residualPtr projected2Ptr
    residual projected2 hHeap hResidual hProjected2 (by rw [hResidualSize, hProjected2Size]) hProjected2Protected
    hResidualProtected hBump hPages
  simp only [hResidualSize, hProjected2Size, hSize, hNeed] at hCall
  rw [emitted_hidden]
  simp only [hiddenCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hParamsLength, hLocals, hValues,
    hResidualOwner, hResidualPtr, hResidualBytes, hProjected2Owner, hProjected2Ptr, hProjected2Bytes]
  refine wp_call_tw hCall ?_
  rintro final values ⟨rfl, hFinalHeap, hOutput, hFrame, hFinalPages, hCapacity⟩
  wp_packed_frame [hParams, hParamsLength, hLocals]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [KernelState, hLocals,
      List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff, and_self]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms hidden_spec

end Project.Gpt2CachedStep.Frozen.CachedBlock
