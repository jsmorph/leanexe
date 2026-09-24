import Project.Gpt2CachedStep.CachedBlock.FrozenExpanded
import Project.Gpt2CachedStep.Activate.FrozenSpec

namespace Project.Gpt2CachedStep.Frozen.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def activatedCode : Wasm.Program :=
  [.localGet 116, .localSet 119, .localGet 117, .localSet 120, .localGet 118, .localSet 121,
   .localGet 119, .localGet 120, .localGet 121, .call 32,
   .localSet 124, .localSet 123, .localSet 122,
   .localGet 122, .localSet 125, .localGet 123, .localSet 126, .localGet 124, .localSet 127]

set_option maxRecDepth 32768 in
theorem emitted_activated : (func33.drop 374).take 19 = activatedCode := rfl

theorem activated_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (expandedPtr : UInt64) (expanded : ByteArray) (frame : Locals)
    (hHeap : heap.At initial) (hExpanded : ByteArrayAt initial.mem expandedPtr.toNat expanded)
    (hExpandedProtected : heap.Protects expandedPtr.toNat (expandedPtr.toNat + expanded.size))
    (hExpandedSize : expanded.size = 12288)
    (hResources : LayerNorm.AllocationFits heap expandedNeed (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = params) (hParamsLength : params.length = 11)
    (hLocals : frame.locals.length = 164) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (hExpandedOwner : frame.locals[105]? = some (.i64 expandedPtr))
    (hExpandedPtr : frame.locals[106]? = some (.i64 expandedPtr))
    (hExpandedBytes : frame.locals[107]? = some (.i64 12288))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState params (frame.locals.take 108) 108 111 114
        (allocatedNode heap.top expandedNeed heap.nodes).root 12288 result →
      (heap.allocate expandedNeed).At final →
      (heap.allocate expandedNeed).OwnsPacked final (allocatedNode heap.top expandedNeed heap.nodes)
        (activate expanded) →
      heap.Frame initial (heap.allocate expandedNeed) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((func33.drop 374).take 19 ++ rest) Q initial frame env := by
  have hNeed : Activate.need expanded = expandedNeed := by rw [Activate.need, hExpandedSize]; rfl
  have hSize : (activate expanded).size = 12288 := by
    rw [activate, PackedSource.generate_size, hExpandedSize]
  have hBump : LayerNorm.AllocationFits heap (Activate.need expanded) (initial.memoryCap «module» 0) := by
    rw [hNeed]
    exact hResources
  have hCall := Activate.Spec.activate_exact env initial heap expandedPtr expandedPtr expanded
    hHeap hExpanded hExpandedProtected hBump hPages
  simp only [hExpandedSize, hSize, hNeed] at hCall
  rw [emitted_activated]
  simp only [activatedCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hParamsLength, hLocals, hValues, hExpandedOwner, hExpandedPtr, hExpandedBytes]
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

#print axioms activated_spec

end Project.Gpt2CachedStep.Frozen.CachedBlock
