import Project.Gpt2QuantizedCached.CachedHidden.FinishSuccessPrepare

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

theorem finishAppend_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (embedding hidden updatesPtr cachePtr : UInt64)
    (hiddenSize : Nat) (updates cache : ByteArray) (frame : Locals)
    (hHeap : heap.At initial)
    (hUpdates : ByteArrayAt initial.mem updatesPtr.toNat updates)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hUpdatesProtected : heap.Protects updatesPtr.toNat (updatesPtr.toNat + updates.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hSize : cache.size + updates.size ≤ 4294967296)
    (hBump : takeFirstFitFrom 0 (PackedAppend.need cache updates) heap.nodes = none →
      heap.top.toNat + 48 + (PackedAppend.need cache updates).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (PackedAppend.need cache updates) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) (hParams : params.length = 8)
    (hState : SuccessFrame params embedding hidden updatesPtr cachePtr hiddenSize updates.size cache.size frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      ResultFrame params embedding updatesPtr 0 hidden
        (allocatedRoot heap.top (PackedAppend.need cache updates) heap.nodes)
        hiddenSize (cache.size + updates.size) result →
      heap.PackedOutput initial final (PackedAppend.need cache updates) (cache ++ updates) →
      wp «module» rest Q final result env) :
    wp «module» (PackedAppend.program 127 ++ finishSuccessResultCode ++ rest) Q initial frame env := by
  have hParamLength : frame.params.length = 8 := by rw [hState.paramsEq, hParams]
  rw [List.append_assoc]
  apply PackedAppend.program_spec 127 «module» env initial heap frame cachePtr updatesPtr cache updates
    hHeap hCache hUpdates hCacheProtected hUpdatesProtected hSize hBump hPages rfl
    (by rw [hParamLength]; decide) (by rw [hParamLength, hState.length]; decide) hState.values hState.typed
  · simpa [Locals.get, hParamLength, hState.length] using hState.leftPtr
  · simpa [Locals.get, hParamLength, hState.length] using hState.leftSize
  · simpa [Locals.get, hParamLength, hState.length] using hState.rightPtr
  · simpa [Locals.get, hParamLength, hState.length] using hState.rightSize
  intro final result hReturned hPreserved hOutput
  have hResultParams : result.params = params := hPreserved.1.trans hState.paramsEq
  have hResultLength : result.locals.length = 144 := hPreserved.2.1.trans hState.length
  have hRead (index : Nat) (hi : index < 119 ∨ 132 ≤ index) :
      result.locals[index]? = frame.locals[index]? :=
    hPreserved.local index (by rw [hParamLength]; omega)
  simp only [finishSuccessResultCode, List.cons_append, List.nil_append]
  wp_packed_frame [hResultParams, hParams, hResultLength, hReturned,
    hRead 108 (by decide), hRead 110 (by decide), hState.oldCacheSize, hState.updateSize,
    ← UInt64.ofNat_add]
  apply hNext
  · constructor <;>
      simp (config := { maxDischargeDepth := 64 }) only [hResultLength,
        List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
        I64Values.set, hPreserved.2.2.1,
        hRead 5 (by decide), hRead 92 (by decide), hRead 93 (by decide),
        hRead 112 (by decide), hRead 113 (by decide), hRead 114 (by decide), hRead 115 (by decide),
        hState.embeddingOwner, hState.updatesOwner, hState.updatesPtr, hState.status,
        hState.hiddenOwner, hState.hiddenPtr, hState.hiddenSize]
  · exact hOutput

#print axioms finishAppend_spec
end Project.Gpt2QuantizedCached.CachedHidden
