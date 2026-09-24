import Project.Gpt2CachedStep.CachedHidden.LayerAppend
import Project.ProofKit.PackedReleaseFilter
import Project.Gpt2CachedStep.Release

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def layerReleaseAction (ownerLocal : Nat) : Wasm.Program :=
  [.localGet ownerLocal, .call 42, .globalGet 5, .localSet 79]

def layerRetainedFilters : Wasm.Program :=
  PackedReleaseFilter.program 49 [52, 75, 72] (layerReleaseAction 49) ++
  PackedReleaseFilter.program 69 [49, 52, 75, 72] (layerReleaseAction 69)

set_option maxRecDepth 32768 in
theorem emitted_layerCacheRelease : (layerBody.drop 155).take 24 =
    PackedReleaseFilter.program 52 [75, 72] (layerReleaseAction 52) ++ layerRetainedFilters := rfl

theorem layerRetainedFilters_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (hidden cache output : UInt64) (hValues : frame.values = [])
    (h49 : frame.get 49 = some (.i64 hidden)) (h52 : frame.get 52 = some (.i64 cache))
    (h69 : frame.get 69 = some (.i64 output)) (h72 : frame.get 72 = some (.i64 hidden))
    (h75 : frame.get 75 = some (.i64 output)) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store frame env) :
    wp «module» (layerRetainedFilters ++ rest) Q store frame env := by
  simp only [layerRetainedFilters, List.append_assoc]
  apply PackedReleaseFilter.program_spec «module» env store frame 49 hidden
    [(52, cache), (75, output), (72, hidden)] (layerReleaseAction 49) hValues h49
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact h52
    · exact h75
    · exact h72
  · intro enabled
    exact False.elim (enabled.2 (72, hidden) (by simp) rfl)
  intro _
  apply PackedReleaseFilter.program_spec «module» env store frame 69 output
    [(49, hidden), (52, cache), (75, output), (72, hidden)] (layerReleaseAction 69) hValues h69
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact h49
    · exact h52
    · exact h75
    · exact h72
  · intro enabled
    exact False.elim (enabled.2 (75, output) (by simp) rfl)
  · intro _
    exact hNext

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
    wp «module» ((layerBody.drop 155).take 24 ++ rest) Q initial frame env := by
  have hParams := hState.1.1
  have hLocals := hState.1.2.1
  have hValues := hState.1.2.2.1
  have hTyped := hState.1.2.2.2.1
  have hHidden49 := hState.2.1
  have hCache52 := hState.2.2.1
  have hOutput69 := hState.2.2.2.1
  have hHidden72 := hState.2.2.2.2.1
  have hOutput75 := hState.2.2.2.2.2.2.2.1
  have hRead49 : frame.get 49 = some (.i64 hiddenPtr) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hHidden49
  have hRead52 : frame.get 52 = some (.i64 cacheNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hCache52
  have hRead69 : frame.get 69 = some (.i64 outputPtr) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hOutput69
  have hRead72 : frame.get 72 = some (.i64 hiddenPtr) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hHidden72
  have hRead75 : frame.get 75 = some (.i64 outputPtr) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hOutput75
  rw [emitted_layerCacheRelease]
  simp only [List.append_assoc]
  apply PackedReleaseFilter.program_spec «module» env initial frame 52 cacheNode.root
    [(75, outputPtr), (72, hiddenPtr)] (layerReleaseAction 52) hValues hRead52
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact hRead75
    · exact hRead72
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
    apply layerRetainedFilters_spec env _ _ hiddenPtr cacheNode.root outputPtr
    · rfl
    · simpa [Locals.get, hParams, hParamsLength, hLocals] using hHidden49
    · simpa [Locals.get, hParams, hParamsLength, hLocals] using hCache52
    · simpa [Locals.get, hParams, hParamsLength, hLocals] using hOutput69
    · simpa [Locals.get, hParams, hParamsLength, hLocals] using hHidden72
    · simpa [Locals.get, hParams, hParamsLength, hLocals] using hOutput75
    apply hNext
    · simpa (config := { maxDischargeDepth := 64 }) only [LayerAppendState, LayerState,
        List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
        I64Values.set, hTyped, hValues, hParams] using hState
    · exact hReleased
  · intro hDisabled
    apply False.elim
    apply hDisabled
    constructor
    · intro hZero
      have hBound := hCache.buffer.rootBound
      rw [hZero] at hBound
      contradiction
    · simpa using And.intro hOutputNe hHiddenNe

#print axioms layerCacheRelease_spec

end Project.Gpt2CachedStep.CachedHidden
