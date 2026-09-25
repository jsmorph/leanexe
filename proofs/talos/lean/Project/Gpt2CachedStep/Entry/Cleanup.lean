import Project.Gpt2CachedStep.Entry.Code

namespace Project.Gpt2CachedStep.Entry
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def cleanupItems (hiddenNode normalizedNode : FreeNode) (hiddenBytes normalizedBytes : ByteArray) : List PackedReleaseMany.Item :=
  [⟨36, normalizedNode, normalizedBytes⟩, ⟨14, hiddenNode, hiddenBytes⟩]

set_option maxRecDepth 32768 in
theorem emitted_cleanup (hiddenNode normalizedNode : FreeNode) (hiddenBytes normalizedBytes : ByteArray) :
    validBody.drop 128 = PackedReleaseMany.program (cleanupItems hiddenNode normalizedNode hiddenBytes normalizedBytes) 54 51 42 := rfl

theorem cleanup_spec (env : HostEnv Unit) (initial original : Store Unit) (heap before : Heap)
    (params : List Value) (hiddenNode normalizedNode cacheNode logitsNode : FreeNode)
    (hiddenBytes normalizedBytes cacheBytes logitsBytes : ByteArray) (frame : Locals)
    (hHeap : heap.At initial)
    (hHidden : heap.OwnsPacked initial hiddenNode hiddenBytes)
    (hNormalized : heap.OwnsPacked initial normalizedNode normalizedBytes)
    (hCache : heap.OwnsPacked initial cacheNode cacheBytes)
    (hLogits : heap.OwnsPacked initial logitsNode logitsBytes)
    (hTemporarySep : regionsDisjoint normalizedNode.region hiddenNode.region)
    (hHiddenCache : regionsDisjoint hiddenNode.region cacheNode.region)
    (hNormalizedCache : regionsDisjoint normalizedNode.region cacheNode.region)
    (hHiddenLogits : regionsDisjoint hiddenNode.region logitsNode.region)
    (hNormalizedLogits : regionsDisjoint normalizedNode.region logitsNode.region)
    (hFrame : before.Frame original heap initial)
    (hHiddenFresh : before.FreshNode hiddenNode) (hNormalizedFresh : before.FreshNode normalizedNode)
    (hParamsLength : params.length = 6)
    (hState : LogitsState params hiddenNode.root normalizedNode.root cacheNode.root logitsNode.root cacheBytes.size frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext :
      (heap.release normalizedNode |>.release hiddenNode).At
        ((heap.release normalizedNode).releaseStore (heap.releaseStore initial normalizedNode) hiddenNode) →
      (heap.release normalizedNode |>.release hiddenNode).OwnsPacked
        ((heap.release normalizedNode).releaseStore (heap.releaseStore initial normalizedNode) hiddenNode) cacheNode cacheBytes →
      (heap.release normalizedNode |>.release hiddenNode).OwnsPacked
        ((heap.release normalizedNode).releaseStore (heap.releaseStore initial normalizedNode) hiddenNode) logitsNode logitsBytes →
      before.Frame original (heap.release normalizedNode |>.release hiddenNode)
        ((heap.release normalizedNode).releaseStore (heap.releaseStore initial normalizedNode) hiddenNode) →
      wp «module» rest Q ((heap.release normalizedNode).releaseStore (heap.releaseStore initial normalizedNode) hiddenNode) frame env) :
    wp «module» (validBody.drop 128 ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨hParams, hLocals, hValues, _⟩, hHidden14, hNorm36, hCache51, _, _, hLogits54, _, _⟩
  have hReadHidden : frame.get 14 = some (.i64 hiddenNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hHidden14
  have hReadNorm : frame.get 36 = some (.i64 normalizedNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hNorm36
  have hReadCache : frame.get 51 = some (.i64 cacheNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hCache51
  have hReadLogits : frame.get 54 = some (.i64 logitsNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hLogits54
  rw [emitted_cleanup hiddenNode normalizedNode hiddenBytes normalizedBytes]
  apply PackedReleaseMany.program_spec env «module» 42 initial heap before original frame
    (cleanupItems hiddenNode normalizedNode hiddenBytes normalizedBytes) logitsNode cacheNode logitsBytes cacheBytes
    54 51 (typeIdx := some 42) rfl rfl hHeap
  · simpa [cleanupItems] using And.intro hNormalized hHidden
  · exact hLogits
  · exact hCache
  · simpa [cleanupItems] using hTemporarySep
  · simpa [cleanupItems] using And.intro hNormalizedLogits hHiddenLogits
  · simpa [cleanupItems] using And.intro hNormalizedCache hHiddenCache
  · exact hFrame
  · simpa [cleanupItems, Heap.FreshNode] using And.intro hNormalizedFresh hHiddenFresh
  · exact hValues
  · simpa [cleanupItems] using And.intro hReadNorm hReadHidden
  · exact hReadLogits
  · exact hReadCache
  intro hFinalHeap hFinalLogits hFinalCache hFinalFrame
  exact hNext hFinalHeap hFinalCache hFinalLogits hFinalFrame

#print axioms cleanup_spec

end Project.Gpt2CachedStep.Entry
