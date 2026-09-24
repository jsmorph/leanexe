import Project.Gpt2CachedStep.CachedHidden.LayerAppend
import Project.ProofKit.PackedReleaseFilter
import Project.Gpt2CachedStep.Release

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def layerReleaseAction (ownerLocal : Nat) : Wasm.Program :=
  [.localGet ownerLocal, .call 42, .globalGet 5, .localSet 79]

set_option maxRecDepth 32768 in
theorem emitted_layerCacheRelease : (layerBody.drop 149).take 8 =
    PackedReleaseFilter.program 52 [72, 75, 78] (layerReleaseAction 52) := rfl

theorem layerCacheRelease_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (embeddingPtr inputPtr updatesPtr hiddenPtr outputPtr : UInt64)
    (cacheNode : FreeNode) (cache : ByteArray) (layer updatesSize : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hCache : heap.OwnsPacked initial cacheNode cache)
    (hHiddenNe : cacheNode.root ≠ hiddenPtr) (hOutputNe : cacheNode.root ≠ outputPtr)
    (hParamsLength : params.length = 8)
    (hState : LayerAppendState params embeddingPtr inputPtr updatesPtr hiddenPtr cacheNode.root outputPtr
      layer updatesSize frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result,
      LayerAppendState params embeddingPtr inputPtr updatesPtr hiddenPtr cacheNode.root outputPtr layer updatesSize result →
      (heap.release cacheNode).At (heap.releaseStore initial cacheNode) →
      wp «module» rest Q (heap.releaseStore initial cacheNode) result env) :
    wp «module» ((layerBody.drop 149).take 8 ++ rest) Q initial frame env := by
  have hParams := hState.1.1
  have hLocals := hState.1.2.1
  have hValues := hState.1.2.2.1
  have hTyped := hState.1.2.2.2.1
  have hCache52 := hState.2.2.1
  have hHidden72 := hState.2.2.2.2.1
  have hOutput75 := hState.2.2.2.2.2.2.2.1
  have hZero78 := hState.2.2.2.2.2.2.2.2.2.2
  have hRead52 : frame.get 52 = some (.i64 cacheNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hCache52
  have hRead72 : frame.get 72 = some (.i64 hiddenPtr) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hHidden72
  have hRead75 : frame.get 75 = some (.i64 outputPtr) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hOutput75
  have hRead78 : frame.get 78 = some (.i64 0) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hZero78
  have hRootNe : cacheNode.root ≠ 0 := by
    intro hZero
    have hBound := hCache.buffer.rootBound
    rw [hZero] at hBound
    contradiction
  rw [emitted_layerCacheRelease]
  apply PackedReleaseFilter.program_spec «module» env initial frame 52 cacheNode.root
    [(72, hiddenPtr), (75, outputPtr), (78, 0)]
    (layerReleaseAction 52) hValues hRead52
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact hRead72
    · exact hRead75
    · exact hRead78
  · intro _
    simp only [layerReleaseAction]
    have hRead52' := hRead52
    simp only [Locals.get] at hRead52'
    wp_packed_frame [hValues, hRead52']
    refine wp_call_tw (Release.release_owned env initial heap cacheNode cache hHeap hCache) ?_
    rintro final values ⟨rfl, rfl, hReleased⟩
    have hFrees : (heap.releaseStore initial cacheNode).globals.globals[5]? = some (.i64 (heap.frees + 1)) := by
      rw [hReleased.globals]
      rfl
    wp_packed_frame [hFrees, hParams, hParamsLength, hLocals, PackedReleaseFilter.afterAction]
    apply hNext
    · simpa (config := { maxDischargeDepth := 64 }) only [LayerAppendState, LayerState,
        List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
        I64Values.set, hTyped, hValues, hParams] using hState
    · exact hReleased
  · intro hDisabled
    apply False.elim
    apply hDisabled
    exact ⟨hRootNe, by simpa using And.intro hHiddenNe (And.intro hOutputNe hRootNe)⟩

#print axioms layerCacheRelease_spec

end Project.Gpt2CachedStep.CachedHidden
