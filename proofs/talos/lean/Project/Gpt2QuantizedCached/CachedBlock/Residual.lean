import Project.Gpt2QuantizedCached.CachedBlock.Projection
import Project.Gpt2QuantizedCached.AddRows
import Project.Gpt2QuantizedCached.CachedBlock.Resources

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def residualCode : Wasm.Program :=
  [.localGet 3, .localSet 89, .localGet 4, .localSet 90, .localGet 5, .localSet 91,
   .localGet 86, .localSet 92, .localGet 87, .localSet 93, .localGet 88, .localSet 94,
   .localGet 89, .localGet 90, .localGet 91, .localGet 92, .localGet 93, .localGet 94,
   .call 51, .localSet 97, .localSet 96, .localSet 95,
   .localGet 95, .localSet 98, .localGet 96, .localSet 99, .localGet 97, .localSet 100]

set_option maxRecDepth 32768 in
theorem emitted_residual : (attentionSuccess.drop 79).take 28 = residualCode := rfl

theorem residual_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr projectedPtr : UInt64)
    (weights input cache projected : ByteArray) (layer position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hProjected : ByteArrayAt initial.mem projectedPtr.toNat projected)
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hProjectedProtected : heap.Protects projectedPtr.toNat (projectedPtr.toNat + projected.size))
    (hInputSize : input.size = 3072) (hProjectedSize : projected.size = 3072)
    (hResources : Gpt2CachedStep.LayerNorm.AllocationFits heap residualNeed (initial.memoryCap Project.Gpt2CachedStep.«module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 193) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (hProjectedOwner : frame.locals[75]? = some (.i64 projectedPtr))
    (hProjectedPtr : frame.locals[76]? = some (.i64 projectedPtr))
    (hProjectedBytes : frame.locals[77]? = some (.i64 3072))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 78) 78 84 87
        (allocatedNode heap.top residualNeed heap.nodes).root 3072 result →
      (heap.allocate residualNeed).At final →
      (heap.allocate residualNeed).OwnsPacked final (allocatedNode heap.top residualNeed heap.nodes)
        (addRows input projected) →
      heap.Frame initial (heap.allocate residualNeed) final →
      final.mem.pages ≤ 65536 → final.memoryCap Project.Gpt2CachedStep.«module» 0 = initial.memoryCap Project.Gpt2CachedStep.«module» 0 →
      wp «module» rest Q final result env) :
    wp «module» (residualCode ++ rest) Q initial frame env := by
  have hNeed : Gpt2CachedStep.AddRows.need input = residualNeed := by rw [Gpt2CachedStep.AddRows.need, hInputSize]; rfl
  have hSize : (addRows input projected).size = 3072 := by
    rw [addRows, PackedSource.generate_size, hInputSize]
  have hBump : Gpt2CachedStep.LayerNorm.AllocationFits heap (Gpt2CachedStep.AddRows.need input) (initial.memoryCap Project.Gpt2CachedStep.«module» 0) := by
    rw [hNeed]
    exact hResources
  have hCall := AddRows.addRows_exact env initial heap inputOwner projectedPtr inputPtr projectedPtr
    input projected hHeap hInput hProjected (by rw [hInputSize, hProjectedSize]) hProjectedProtected
    hInputProtected hBump hPages
  simp only [hInputSize, hProjectedSize, hSize, hNeed] at hCall
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

end Project.Gpt2QuantizedCached.CachedBlock
