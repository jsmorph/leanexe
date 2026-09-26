import Project.Gpt2QuantizedCached.Entry.OutputFailure

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

def outputRejected (cache logits : ByteArray) (position : Nat) : Bool :=
  !finiteWords cache 0 ((position + 1) * cachePositionWords) || !finiteWords logits 0 50257

def outputResult (cache logits : ByteArray) (position : Nat) : CachedResult :=
  if outputRejected cache logits position then ⟨4, .empty, .empty⟩ else ⟨0, cache, logits⟩

def outputHeap (heap : Heap) (cache logits : FreeNode) (rejected : Bool) : Heap :=
  if rejected then (heap.release logits).release cache else heap

def outputStore (heap : Heap) (store : Store Unit) (cache logits : FreeNode) (rejected : Bool) : Store Unit :=
  if rejected then (heap.release logits).releaseStore (heap.releaseStore store logits) cache else store

theorem outputResult_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr hiddenPtr normalizedPtr : UInt64)
    (cacheNode logitsNode : FreeNode) (weights cache outputCache logits : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hCache : heap.OwnsPacked initial cacheNode outputCache)
    (hLogits : heap.OwnsPacked initial logitsNode logits)
    (hCacheFresh : before.FreshNode cacheNode) (hLogitsFresh : before.FreshNode logitsNode)
    (hSeparated : regionsDisjoint cacheNode.region logitsNode.region)
    (hFrame : before.Frame original heap initial)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.memoryCap «module» 0 = original.memoryCap «module» 0)
    (hSize : (position + 1) * cachePositionWords * 4 ≤ outputCache.size)
    (hLogitsSize : logits.size = 201028) (hPosition : position < 128)
    (hState : LogitsState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      hiddenPtr cacheNode.root normalizedPtr logitsNode.root outputCache.size frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result,
      let output := outputResult outputCache logits position
      ResultState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        output.status (statusRoot output.status cacheNode) (statusRoot output.status logitsNode)
        output.cache.size output.logits.size result →
      result.locals[17]? = some (.i64 hiddenPtr) → result.locals[39]? = some (.i64 normalizedPtr) →
      Completion before original (outputHeap heap cacheNode logitsNode (outputRejected outputCache logits position))
        (outputStore heap initial cacheNode logitsNode (outputRejected outputCache logits position))
        output.status cacheNode logitsNode output.cache output.logits →
      wp «module» rest Q (outputStore heap initial cacheNode logitsNode (outputRejected outputCache logits position)) result env) :
    wp «module» (outputTestCode ++ [.iff 0 0 outputFailureCode successResultCode] ++ rest) Q initial frame env := by
  apply outputGuard_spec env initial weightsOwner weightsPtr cacheOwner cachePtr hiddenPtr cacheNode.root
    normalizedPtr logitsNode.root weights cache outputCache logits token position frame
    hCache.buffer.values hLogits.buffer.values hSize hLogitsSize hPosition hState
  intro checked hChecked
  change wp «module» (if outputRejected outputCache logits position then outputFailureCode else successResultCode)
    _ initial checked env
  cases hRejected : outputRejected outputCache logits position
  · simp only [hRejected, Bool.false_eq_true, ite_false]
    rw [← List.append_nil successResultCode]
    apply successResult_spec env initial _ hiddenPtr cacheNode.root normalizedPtr logitsNode.root
      outputCache.size checked (by rfl) hChecked
    intro result hResult hPrefix
    simp only [wp_nil, PackedReleaseFilter.afterAction]
    have hCacheStatus : heap.StatusPacked initial 0 cacheNode outputCache := ⟨fun _ => hCache, by simp⟩
    have hLogitsStatus : heap.StatusPacked initial 0 logitsNode logits := ⟨fun _ => hLogits, by simp⟩
    have hMemory : Completion before original heap initial 0 cacheNode logitsNode outputCache logits :=
      ⟨hHeap, hCacheStatus, hLogitsStatus, hFrame, fun _ => hCacheFresh, fun _ => hLogitsFresh,
        fun _ => hSeparated, hPages, hCap⟩
    have hRun := hNext result
    simp only [outputResult, hRejected, Bool.false_eq_true, ite_false, outputHeap, outputStore,
      statusRoot, hLogitsSize, show (0 : UInt64) = 0 from rfl] at hRun
    have hRun' := hRun hResult
      ((Frame.local_of_take_eq hPrefix (by decide)).trans hChecked.releaseHidden)
      ((Frame.local_of_take_eq hPrefix (by decide)).trans hChecked.releaseNormalized) hMemory
    simpa only [← hResult.values] using hRun'
  · simp only [hRejected, ite_true]
    rw [← List.append_nil outputFailureCode]
    apply failureOutput_spec env original initial before heap _ hiddenPtr normalizedPtr cacheNode logitsNode
      outputCache logits checked hHeap hCache hLogits hCacheFresh hLogitsFresh hSeparated hFrame hPages hCap
      (by rfl) hChecked
    intro result hResult hPrefix hMemory
    simp only [wp_nil, PackedReleaseFilter.afterAction]
    have hRun := hNext result
    simp only [outputResult, hRejected, ite_true, outputHeap, outputStore, statusRoot,
      show (4 : UInt64) ≠ 0 by decide, ite_false, ByteArray.size_empty] at hRun
    have hRun' := hRun hResult
      ((Frame.local_of_take_eq hPrefix (by decide)).trans hChecked.releaseHidden)
      ((Frame.local_of_take_eq hPrefix (by decide)).trans hChecked.releaseNormalized) hMemory
    simpa only [← hResult.values] using hRun'

#print axioms outputResult_spec
end Project.Gpt2QuantizedCached.Entry
