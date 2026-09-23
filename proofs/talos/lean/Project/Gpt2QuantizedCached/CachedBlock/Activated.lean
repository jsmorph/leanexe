import Project.Gpt2QuantizedCached.CachedBlock.Expanded
import Project.Gpt2QuantizedCached.Activate
import Project.Gpt2QuantizedCached.CachedBlock.Resources

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def activatedCode : Wasm.Program :=
  [.localGet 137, .localSet 140, .localGet 138, .localSet 141, .localGet 139, .localSet 142,
   .localGet 140, .localGet 141, .localGet 142, .call 53,
   .localSet 145, .localSet 144, .localSet 143,
   .localGet 143, .localSet 146, .localGet 144, .localSet 147, .localGet 145, .localSet 148]

set_option maxRecDepth 32768 in
theorem emitted_activated : (normalized2Success.drop 79).take 19 = activatedCode := rfl

theorem activated_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (expandedPtr : UInt64) (expanded : ByteArray) (frame : Locals)
    (hHeap : heap.At initial) (hExpanded : ByteArrayAt initial.mem expandedPtr.toNat expanded)
    (hExpandedProtected : heap.Protects expandedPtr.toNat (expandedPtr.toNat + expanded.size))
    (hExpandedSize : expanded.size = 12288)
    (hResources : Gpt2CachedStep.LayerNorm.AllocationFits heap activatedNeed (initial.memoryCap Project.Gpt2CachedStep.«module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = params) (hParamsLength : params.length = 11)
    (hLocals : frame.locals.length = 193) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (hExpandedOwner : frame.locals[126]? = some (.i64 expandedPtr))
    (hExpandedPtr : frame.locals[127]? = some (.i64 expandedPtr))
    (hExpandedBytes : frame.locals[128]? = some (.i64 12288))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState params (frame.locals.take 129) 129 132 135
        (allocatedNode heap.top activatedNeed heap.nodes).root 12288 result →
      (heap.allocate activatedNeed).At final →
      (heap.allocate activatedNeed).OwnsPacked final (allocatedNode heap.top activatedNeed heap.nodes)
        (activate expanded) →
      heap.Frame initial (heap.allocate activatedNeed) final →
      final.mem.pages ≤ 65536 → final.memoryCap Project.Gpt2CachedStep.«module» 0 = initial.memoryCap Project.Gpt2CachedStep.«module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((normalized2Success.drop 79).take 19 ++ rest) Q initial frame env := by
  have hNeed : Gpt2CachedStep.Activate.need expanded = activatedNeed := by rw [Gpt2CachedStep.Activate.need, hExpandedSize]; rfl
  have hSize : (activate expanded).size = 12288 := by
    rw [activate, PackedSource.generate_size, hExpandedSize]
  have hBump : Gpt2CachedStep.LayerNorm.AllocationFits heap (Gpt2CachedStep.Activate.need expanded) (initial.memoryCap Project.Gpt2CachedStep.«module» 0) := by
    rw [hNeed]
    exact hResources
  have hCall := Activate.activate_exact env initial heap expandedPtr expandedPtr expanded
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

end Project.Gpt2QuantizedCached.CachedBlock
