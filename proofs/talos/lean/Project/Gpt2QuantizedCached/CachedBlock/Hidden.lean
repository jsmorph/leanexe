import Project.Gpt2QuantizedCached.CachedBlock.Residual

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def hiddenCode : Wasm.Program :=
  [.localGet 98, .localSet 173, .localGet 99, .localSet 174, .localGet 100, .localSet 175,
   .localGet 170, .localSet 176, .localGet 171, .localSet 177, .localGet 172, .localSet 178,
   .localGet 173, .localGet 174, .localGet 175, .localGet 176, .localGet 177, .localGet 178,
   .call 51, .localSet 181, .localSet 180, .localSet 179,
   .localGet 179, .localSet 190, .localGet 180, .localSet 191, .localGet 181, .localSet 192]

set_option maxRecDepth 32768 in
theorem emitted_hidden : (activatedSuccess.drop 81).take 28 = hiddenCode := rfl

theorem hidden_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (residualPtr projected2Ptr : UInt64) (residual projected2 : ByteArray) (frame : Locals)
    (hHeap : heap.At initial)
    (hResidual : ByteArrayAt initial.mem residualPtr.toNat residual)
    (hProjected2 : ByteArrayAt initial.mem projected2Ptr.toNat projected2)
    (hResidualProtected : heap.Protects residualPtr.toNat (residualPtr.toNat + residual.size))
    (hProjected2Protected : heap.Protects projected2Ptr.toNat (projected2Ptr.toNat + projected2.size))
    (hResidualSize : residual.size = 3072) (hProjected2Size : projected2.size = 3072)
    (hResources : Gpt2CachedStep.LayerNorm.AllocationFits heap residualNeed (initial.memoryCap Project.Gpt2CachedStep.«module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = params) (hParamsLength : params.length = 11)
    (hLocals : frame.locals.length = 193) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (hResidualOwner : frame.locals[87]? = some (.i64 residualPtr))
    (hResidualPtr : frame.locals[88]? = some (.i64 residualPtr))
    (hResidualBytes : frame.locals[89]? = some (.i64 3072))
    (hProjected2Owner : frame.locals[159]? = some (.i64 projected2Ptr))
    (hProjected2Ptr : frame.locals[160]? = some (.i64 projected2Ptr))
    (hProjected2Bytes : frame.locals[161]? = some (.i64 3072))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState params (frame.locals.take 162) 162 168 179
        (allocatedNode heap.top residualNeed heap.nodes).root 3072 result →
      result.locals[178]? = frame.locals[178]? →
      (heap.allocate residualNeed).At final →
      (heap.allocate residualNeed).OwnsPacked final (allocatedNode heap.top residualNeed heap.nodes)
        (addRows residual projected2) →
      heap.Frame initial (heap.allocate residualNeed) final →
      final.mem.pages ≤ 65536 → final.memoryCap Project.Gpt2CachedStep.«module» 0 = initial.memoryCap Project.Gpt2CachedStep.«module» 0 →
      wp «module» rest Q final result env) :
    wp «module» (hiddenCode ++ rest) Q initial frame env := by
  have hNeed : Gpt2CachedStep.AddRows.need residual = residualNeed := by rw [Gpt2CachedStep.AddRows.need, hResidualSize]; rfl
  have hSize : (addRows residual projected2).size = 3072 := by
    rw [addRows, PackedSource.generate_size, hResidualSize]
  have hBump : Gpt2CachedStep.LayerNorm.AllocationFits heap (Gpt2CachedStep.AddRows.need residual) (initial.memoryCap Project.Gpt2CachedStep.«module» 0) := by
    rw [hNeed]
    exact hResources
  have hCall := AddRows.addRows_exact env initial heap residualPtr projected2Ptr residualPtr projected2Ptr
    residual projected2 hHeap hResidual hProjected2 (by rw [hResidualSize, hProjected2Size]) hProjected2Protected
    hResidualProtected hBump hPages
  simp only [hResidualSize, hProjected2Size, hSize, hNeed] at hCall
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
  · simp only [List.getElem?_set, List.length_set, hLocals, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms hidden_spec

end Project.Gpt2QuantizedCached.CachedBlock
