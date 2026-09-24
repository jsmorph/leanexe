import Project.Gpt2CachedStep.Entry.Code
import Project.ProofKit.PackedReleaseManyAliases

namespace Project.Gpt2CachedStep.Entry
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def cleanupItems (hiddenNode normalizedNode : FreeNode) (hiddenBytes normalizedBytes : ByteArray) : List PackedReleaseMany.Item :=
  [⟨36, normalizedNode, normalizedBytes⟩, ⟨14, hiddenNode, hiddenBytes⟩]

def cleanupKept (owner : Nat) : List Nat :=
  if owner = 36 then [51, 54, 23, 20, 14, 17, 9, 6] else [51, 54]

set_option maxRecDepth 32768 in
theorem emitted_cleanup (hiddenNode normalizedNode : FreeNode) (hiddenBytes normalizedBytes : ByteArray) :
    validBody.drop 128 = PackedReleaseManyAliases.program (cleanupItems hiddenNode normalizedNode hiddenBytes normalizedBytes) cleanupKept 42 := rfl

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
  rcases hState with ⟨⟨hParams, hLocals, hValues, _⟩, hHidden14, hNorm36, hCache51, _, _, hLogits54, _, _, hHidden20, hCache23, hCache17, hEmpty6, hEmpty9⟩
  have hReadHidden : frame.get 14 = some (.i64 hiddenNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hHidden14
  have hReadNorm : frame.get 36 = some (.i64 normalizedNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hNorm36
  have hReadCache : frame.get 51 = some (.i64 cacheNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hCache51
  have hReadLogits : frame.get 54 = some (.i64 logitsNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hLogits54
  have hRead20 : frame.get 20 = some (.i64 hiddenNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hHidden20
  have hRead23 : frame.get 23 = some (.i64 cacheNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hCache23
  have hRead17 : frame.get 17 = some (.i64 cacheNode.root) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hCache17
  have hRead6 : frame.get 6 = some (.i64 0) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hEmpty6
  have hRead9 : frame.get 9 = some (.i64 0) := by simpa [Locals.get, hParams, hParamsLength, hLocals] using hEmpty9
  have hNormNonzero : normalizedNode.root ≠ 0 := by
    intro hz
    have := hNormalized.buffer.rootBound
    simp [hz] at this
  rw [emitted_cleanup hiddenNode normalizedNode hiddenBytes normalizedBytes]
  apply PackedReleaseManyAliases.program_spec env «module» 42 initial heap before original frame
    (cleanupItems hiddenNode normalizedNode hiddenBytes normalizedBytes) logitsNode cacheNode logitsBytes cacheBytes
    cleanupKept (typeIdx := some 42) rfl rfl hHeap
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
  · intro item hItem slot hSlot
    simp only [cleanupItems, List.mem_cons, List.not_mem_nil, or_false] at hItem
    rcases hItem with rfl | rfl
    · simp only [cleanupKept, reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hSlot
      rcases hSlot with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨cacheNode.root, hReadCache, hNormalized.root_ne hNormalizedCache⟩
      · exact ⟨logitsNode.root, hReadLogits, hNormalized.root_ne hNormalizedLogits⟩
      · exact ⟨cacheNode.root, hRead23, hNormalized.root_ne hNormalizedCache⟩
      · exact ⟨hiddenNode.root, hRead20, hNormalized.root_ne hTemporarySep⟩
      · exact ⟨hiddenNode.root, hReadHidden, hNormalized.root_ne hTemporarySep⟩
      · exact ⟨cacheNode.root, hRead17, hNormalized.root_ne hNormalizedCache⟩
      · exact ⟨0, hRead9, hNormNonzero⟩
      · exact ⟨0, hRead6, hNormNonzero⟩
    · simp only [cleanupKept, Nat.reduceEqDiff, reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hSlot
      rcases hSlot with rfl | rfl
      · exact ⟨cacheNode.root, hReadCache, hHidden.root_ne hHiddenCache⟩
      · exact ⟨logitsNode.root, hReadLogits, hHidden.root_ne hHiddenLogits⟩
  intro hFinalHeap hFinalLogits hFinalCache hFinalFrame
  exact hNext hFinalHeap hFinalCache hFinalLogits hFinalFrame

#print axioms cleanup_spec

end Project.Gpt2CachedStep.Entry
