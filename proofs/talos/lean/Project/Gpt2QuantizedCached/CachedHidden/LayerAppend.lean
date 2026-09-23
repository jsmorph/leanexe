import Project.Gpt2QuantizedCached.CachedHidden.LayerCall

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

structure AppendedFrame (params : List Value) (embedding input updates hidden cache newUpdates : UInt64)
    (inputSize updateBytes : Nat) (inputStatus : UInt64) (layer : Nat) (output : HiddenResult)
    (frame : Locals) : Prop
    extends LayerFrame params embedding input updates inputSize updateBytes inputStatus layer frame where
  cacheOwner : frame.locals[49]? = some (.i64 cache)
  outputHiddenOwner : frame.locals[71]? = some (.i64 hidden)
  outputHiddenPtr : frame.locals[72]? = some (.i64 hidden)
  outputHiddenSize : frame.locals[73]? = some (.i64 (UInt64.ofNat output.hidden.size))
  outputUpdatesOwner : frame.locals[74]? = some (.i64 newUpdates)
  outputUpdatesPtr : frame.locals[75]? = some (.i64 newUpdates)
  outputUpdatesSize : frame.locals[76]? = some (.i64 (UInt64.ofNat (updateBytes + output.cache.size)))
  outputStatus : frame.locals[77]? = some (.i64 output.status)

theorem layerAppend_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (embedding input updatesPtr hidden cachePtr : UInt64)
    (inputSize : Nat) (updates : ByteArray) (status : UInt64) (layer : Nat)
    (output : HiddenResult) (frame : Locals)
    (hHeap : heap.At initial)
    (hUpdates : ByteArrayAt initial.mem updatesPtr.toNat updates)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat output.cache)
    (hUpdatesProtected : heap.Protects updatesPtr.toNat (updatesPtr.toNat + updates.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + output.cache.size))
    (hSize : updates.size + output.cache.size ≤ 4294967296)
    (hBump : takeFirstFitFrom 0 (PackedAppend.need updates output.cache) heap.nodes = none →
      heap.top.toNat + 48 + (PackedAppend.need updates output.cache).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (PackedAppend.need updates output.cache) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) (hParams : params.length = 8)
    (hState : CalledFrame params embedding input updatesPtr hidden cachePtr
      inputSize updates.size status layer output frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      AppendedFrame params embedding input updatesPtr hidden cachePtr
        (allocatedRoot heap.top (PackedAppend.need updates output.cache) heap.nodes)
        inputSize updates.size status layer output result →
      heap.PackedOutput initial final (PackedAppend.need updates output.cache) (updates ++ output.cache) →
      wp «module» rest Q final result env) :
    wp «module» (PackedAppend.program 130 ++ layerResultCode ++ rest) Q initial frame env := by
  have hParamLength : frame.params.length = 8 := by rw [hState.paramsEq, hParams]
  rw [List.append_assoc]
  apply PackedAppend.program_spec 130 «module» env initial heap frame updatesPtr cachePtr updates output.cache
    hHeap hUpdates hCache hUpdatesProtected hCacheProtected hSize hBump hPages rfl
    (by rw [hParamLength]; decide) (by rw [hParamLength, hState.length]; decide) hState.values hState.typed
  · simpa [Locals.get, hParamLength, hState.length] using hState.leftPtr
  · simpa [Locals.get, hParamLength, hState.length] using hState.leftSize
  · simpa [Locals.get, hParamLength, hState.length] using hState.rightPtr
  · simpa [Locals.get, hParamLength, hState.length] using hState.rightSize
  intro final result hReturned hPreserved hOutput
  have hResultParams : result.params = params := hPreserved.1.trans hState.paramsEq
  have hResultLength : result.locals.length = 144 := hPreserved.2.1.trans hState.length
  have hRead (index : Nat) (hi : index < 122 ∨ 135 ≤ index) :
      result.locals[index]? = frame.locals[index]? :=
    hPreserved.local index (by rw [hParamLength]; omega)
  simp only [layerResultCode, List.cons_append, List.nil_append]
  wp_packed_frame [hResultParams, hParams, hResultLength, hReturned,
    hRead 59 (by decide), hRead 60 (by decide), hRead 61 (by decide), hRead 62 (by decide),
    hRead 64 (by decide), hRead 66 (by decide), hState.outputStatus,
    hState.outputHiddenOwner, hState.outputHiddenPtr, hState.outputHiddenSize, hState.oldSize, hState.blockSize,
    ← UInt64.ofNat_add]
  apply hNext
  · constructor
    · constructor <;>
        simp (config := { maxDischargeDepth := 64 }) only [hResultParams, hResultLength,
          List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
          I64Values.set, hPreserved.2.2.1,
          hRead 5 (by decide), hRead 6 (by decide), hRead 7 (by decide), hRead 80 (by decide), hRead 83 (by decide), hRead 15 (by decide), hRead 16 (by decide), hRead 17 (by decide), hRead 18 (by decide), hRead 19 (by decide), hRead 20 (by decide), hRead 21 (by decide), hRead 119 (by decide), hRead 120 (by decide), hRead 121 (by decide), hRead 143 (by decide),
          hState.toLayerFrame.embeddingOwner, hState.toLayerFrame.embeddingPtr, hState.toLayerFrame.embeddingSize, hState.toLayerFrame.protectedEmbedding, hState.toLayerFrame.protectedUpdates, hState.toLayerFrame.hiddenOwner, hState.toLayerFrame.hiddenPtr, hState.toLayerFrame.hiddenSize, hState.toLayerFrame.updatesOwner, hState.toLayerFrame.updatesPtr, hState.toLayerFrame.updatesSize, hState.toLayerFrame.status, hState.toLayerFrame.counter, hState.toLayerFrame.limit, hState.toLayerFrame.step, hState.toLayerFrame.flag]
    all_goals simp only [hResultLength, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      hRead 49 (by decide), hState.cacheOwner]
  · exact hOutput

#print axioms layerAppend_spec
end Project.Gpt2QuantizedCached.CachedHidden
