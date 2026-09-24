import Project.Gpt2CachedStep.CachedBlock.Qkv
import Project.Gpt2CachedStep.CachedAttention.Spec

namespace Project.Gpt2CachedStep.CachedBlock
open Wasm Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def AttentionState (params : List Value) (base : Nat) (normalizedPtr qkvPtr attentionPtr : UInt64)
    (frame : Locals) : Prop :=
  QkvState params base normalizedPtr qkvPtr frame ∧
  frame.locals[41]? = some (.i64 attentionPtr) ∧ frame.locals[42]? = some (.i64 attentionPtr) ∧
  frame.locals[43]? = some (.i64 3072) ∧ frame.locals[44]? = some (.i64 attentionPtr) ∧
  frame.locals[45]? = some (.i64 attentionPtr) ∧ frame.locals[46]? = some (.i64 3072) ∧
  frame.locals[36]? = some (.i64 qkvPtr)

def attentionCode : Wasm.Program :=
  [.localGet 6, .localSet 44, .localGet 7, .localSet 45, .localGet 8, .localSet 46,
   .localGet 41, .localSet 47, .localGet 42, .localSet 48, .localGet 43, .localSet 49,
   .localGet 9, .localSet 50, .localGet 10, .localSet 51,
   .localGet 44, .localGet 45, .localGet 46, .localGet 47, .localGet 48, .localGet 49,
   .localGet 50, .localGet 51, .call 29,
   .localSet 54, .localSet 53, .localSet 52,
   .localGet 52, .localSet 55, .localGet 53, .localSet 56, .localGet 54, .localSet 57]

set_option maxRecDepth 32768 in
theorem emitted_attention : (func33.drop 129).take 34 = attentionCode := rfl

theorem attention_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr normalizedPtr qkvPtr : UInt64)
    (weights input cache qkv : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache) (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hQkvProtected : heap.Protects qkvPtr.toNat (qkvPtr.toNat + qkv.size))
    (hLayer : layer < 12) (hPosition : position < 128)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : qkv.size = 9216)
    (hResources : CachedAttention.Resources heap position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : QkvState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position) base normalizedPtr qkvPtr frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      AttentionState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) base normalizedPtr qkvPtr
        (CachedAttention.outputNode heap position).root result →
      (CachedAttention.finalHeap heap position).At final →
      (CachedAttention.finalHeap heap position).OwnsPacked final (CachedAttention.outputNode heap position)
        (cachedAttention cache qkv layer position) →
      heap.Frame initial (CachedAttention.finalHeap heap position) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((func33.drop 129).take 34 ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨hParams, hLocals, hValues, hBase, hNormalizedOwner, hNormalizedPtr,
    hNormalizedBytes, hCopiedOwner, hCopiedPtr, hCopiedBytes, hTyped⟩,
    hQkvOwner, hQkvPtr, hQkvBytes, hQkvCopiedOwner, hQkvCopiedPtr, hQkvCopiedBytes, hNormalizedArgument⟩
  have hCall := CachedAttention.Spec.cachedAttention_exact env initial heap cacheOwner qkvPtr cachePtr qkvPtr
    cache qkv layer position hHeap hCache hQkv hCacheProtected hQkvProtected hLayer hPosition
    hCacheSize (by rw [hQkvSize]) hResources hPages
  simp only [hQkvSize] at hCall
  rw [emitted_attention]
  simp only [attentionCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hQkvCopiedOwner, hQkvCopiedPtr, hQkvCopiedBytes]
  refine wp_call_tw hCall ?_
  rintro final values ⟨hReturned, hFinalHeap, hOutput, hFrame, hFinalPages, hCapacity⟩
  rw [CachedAttention.Spec.cachedAttention_size] at hReturned
  subst values
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [AttentionState, QkvState, NormalizedState, parameters,
      hLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte, hBase,
      hNormalizedOwner, hNormalizedPtr, hNormalizedBytes, hCopiedOwner, hCopiedPtr, hCopiedBytes,
      hQkvOwner, hQkvPtr, hQkvBytes, hQkvCopiedOwner, hQkvCopiedPtr, hQkvCopiedBytes, hNormalizedArgument,
      I64Values.set, hTyped, show UInt64.ofNat 3072 = 3072 from rfl, and_self]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms attention_spec

end Project.Gpt2CachedStep.CachedBlock
