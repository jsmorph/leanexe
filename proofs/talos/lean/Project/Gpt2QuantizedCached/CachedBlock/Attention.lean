import Project.Gpt2QuantizedCached.CachedBlock.Qkv
import Project.Gpt2QuantizedCached.CachedAttention

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def AttentionState (params : List Value) (base : Nat) (normalizedPtr qkvPtr attentionPtr : UInt64)
    (frame : Locals) : Prop :=
  QkvState params base normalizedPtr qkvPtr frame ∧
  frame.locals[48]? = some (.i64 attentionPtr) ∧ frame.locals[49]? = some (.i64 attentionPtr) ∧
  frame.locals[50]? = some (.i64 3072) ∧ frame.locals[51]? = some (.i64 attentionPtr) ∧
  frame.locals[52]? = some (.i64 attentionPtr) ∧ frame.locals[53]? = some (.i64 3072)

def attentionCode : Wasm.Program :=
  [.localGet 6, .localSet 51, .localGet 7, .localSet 52, .localGet 8, .localSet 53,
   .localGet 48, .localSet 54, .localGet 49, .localSet 55, .localGet 50, .localSet 56,
   .localGet 9, .localSet 57, .localGet 10, .localSet 58,
   .localGet 51, .localGet 52, .localGet 53, .localGet 54, .localGet 55, .localGet 56,
   .localGet 57, .localGet 58, .call 50,
   .localSet 61, .localSet 60, .localSet 59,
   .localGet 59, .localSet 62, .localGet 60, .localSet 63, .localGet 61, .localSet 64]

set_option maxRecDepth 32768 in
theorem emitted_attention : (normalizedSuccess.drop 79).take 34 = attentionCode := rfl

theorem attention_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr normalizedPtr qkvPtr : UInt64)
    (weights input cache qkv : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache) (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hQkvProtected : heap.Protects qkvPtr.toNat (qkvPtr.toNat + qkv.size))
    (hLayer : layer < 12) (hPosition : position < 128)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : qkv.size = 9216)
    (hResources : Gpt2CachedStep.CachedAttention.Resources heap position (initial.memoryCap Project.Gpt2CachedStep.«module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : QkvState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position) base normalizedPtr qkvPtr frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      AttentionState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) base normalizedPtr qkvPtr
        (Gpt2CachedStep.CachedAttention.outputNode heap position).root result →
      (Gpt2CachedStep.CachedAttention.finalHeap heap position).At final →
      (Gpt2CachedStep.CachedAttention.finalHeap heap position).OwnsPacked final (Gpt2CachedStep.CachedAttention.outputNode heap position)
        (cachedAttention cache qkv layer position) →
      heap.Frame initial (Gpt2CachedStep.CachedAttention.finalHeap heap position) final →
      final.mem.pages ≤ 65536 → final.memoryCap Project.Gpt2CachedStep.«module» 0 = initial.memoryCap Project.Gpt2CachedStep.«module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((normalizedSuccess.drop 79).take 34 ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨hParams, hLocals, hValues, hBase, hNormalizedOwner, hNormalizedPtr,
    hNormalizedBytes, hCopiedOwner, hCopiedPtr, hCopiedBytes, hTyped⟩,
    hQkvOwner, hQkvPtr, hQkvBytes, hQkvCopiedOwner, hQkvCopiedPtr, hQkvCopiedBytes⟩
  have hCall := CachedAttention.cachedAttention_exact env initial heap cacheOwner qkvPtr cachePtr qkvPtr
    cache qkv layer position hHeap hCache hQkv hCacheProtected hQkvProtected hLayer hPosition
    hCacheSize (by rw [hQkvSize]) hResources hPages
  simp only [hQkvSize] at hCall
  rw [emitted_attention]
  simp only [attentionCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hQkvCopiedOwner, hQkvCopiedPtr, hQkvCopiedBytes]
  refine wp_call_tw hCall ?_
  rintro final values ⟨hReturned, hFinalHeap, hOutput, hFrame, hFinalPages, hCapacity⟩
  rw [Gpt2CachedStep.CachedAttention.Spec.cachedAttention_size] at hReturned
  subst values
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [AttentionState, QkvState, NormalizedState, parameters,
      hLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte, hBase,
      hNormalizedOwner, hNormalizedPtr, hNormalizedBytes, hCopiedOwner, hCopiedPtr, hCopiedBytes,
      hQkvOwner, hQkvPtr, hQkvBytes, hQkvCopiedOwner, hQkvCopiedPtr, hQkvCopiedBytes,
      I64Values.set, hTyped, show UInt64.ofNat 3072 = 3072 from rfl, and_self]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms attention_spec

end Project.Gpt2QuantizedCached.CachedBlock
