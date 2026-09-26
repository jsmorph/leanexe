import Project.Gpt2CachedStep.CachedBlock.FrozenProjection
import Project.Gpt2CachedStep.AddRows.FrozenSpec

namespace Project.Gpt2CachedStep.Frozen.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def residualCode : Wasm.Program :=
  [.localGet 3, .localSet 75, .localGet 4, .localSet 76, .localGet 5, .localSet 77,
   .localGet 72, .localSet 78, .localGet 73, .localSet 79, .localGet 74, .localSet 80,
   .localGet 75, .localGet 76, .localGet 77, .localGet 78, .localGet 79, .localGet 80,
   .call 30, .localSet 83, .localSet 82, .localSet 81,
   .localGet 81, .localSet 84, .localGet 82, .localSet 85, .localGet 83, .localSet 86]

set_option maxRecDepth 32768 in
theorem emitted_residual : (func33.drop 226).take 28 = residualCode := rfl

theorem residual_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr projectedPtr : UInt64)
    (weights input cache projected : ByteArray) (layer position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hProjected : ByteArrayAt initial.mem projectedPtr.toNat projected)
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hProjectedProtected : heap.Protects projectedPtr.toNat (projectedPtr.toNat + projected.size))
    (hInputSize : input.size = 3072) (hProjectedSize : projected.size = 3072)
    (hResources : LayerNorm.AllocationFits heap projectionNeed (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 164) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (hProjectedOwner : frame.locals[61]? = some (.i64 projectedPtr))
    (hProjectedPtr : frame.locals[62]? = some (.i64 projectedPtr))
    (hProjectedBytes : frame.locals[63]? = some (.i64 3072))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 64) 64 70 73
        (allocatedNode heap.top projectionNeed heap.nodes).root 3072 result →
      (heap.allocate projectionNeed).At final →
      (heap.allocate projectionNeed).OwnsPacked final (allocatedNode heap.top projectionNeed heap.nodes)
        (addRows input projected) →
      heap.Frame initial (heap.allocate projectionNeed) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((func33.drop 226).take 28 ++ rest) Q initial frame env := by
  have hNeed : AddRows.need input = projectionNeed := by rw [AddRows.need, hInputSize]; rfl
  have hSize : (addRows input projected).size = 3072 := by
    rw [addRows, PackedSource.generate_size, hInputSize]
  have hBump : LayerNorm.AllocationFits heap (AddRows.need input) (initial.memoryCap «module» 0) := by
    rw [hNeed]
    exact hResources
  have hCall := AddRows.Spec.addRows_exact env initial heap inputOwner projectedPtr inputPtr projectedPtr
    input projected hHeap hInput hProjected (by rw [hInputSize, hProjectedSize]) hProjectedProtected
    hInputProtected hBump hPages
  simp only [hInputSize, hProjectedSize, hSize, hNeed] at hCall
  rw [emitted_residual]
  simp only [residualCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hInputSize,
    hProjectedOwner, hProjectedPtr, hProjectedBytes]
  refine wp_call_tw hCall ?_
  rintro final values ⟨rfl, hFinalHeap, hOutput, hFrame, hFinalPages, hCapacity⟩
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [KernelState, parameters, hInputSize, hLocals,
      List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff, and_self]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms residual_spec

end Project.Gpt2CachedStep.Frozen.CachedBlock
