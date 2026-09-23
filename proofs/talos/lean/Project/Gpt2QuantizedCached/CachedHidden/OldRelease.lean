import Project.Gpt2QuantizedCached.CachedHidden.ReleasePending

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem oldRelease_owned_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (params : List Value) (embedding : UInt64) (inputNode oldUpdates hidden update : FreeNode)
    (inputBytes oldUpdateBytes hiddenBytes updateBytes : ByteArray) (outputStatus : UInt64)
    (layer : Nat) (frame : Locals) (hParams : params.length = 8)
    (hMemory : PendingOutput before original heap initial outputStatus hidden update hiddenBytes updateBytes)
    (hState : SelectedFrame params embedding inputNode.root oldUpdates.root
      (statusRoot outputStatus hidden) update.root inputBytes.size oldUpdateBytes.size 0 layer
      hiddenBytes.size updateBytes.size outputStatus frame)
    (hInput : heap.OwnsPacked initial inputNode inputBytes)
    (hOldUpdates : heap.OwnsPacked initial oldUpdates oldUpdateBytes)
    (hInputFresh : before.FreshNode inputNode) (hUpdatesFresh : before.FreshNode oldUpdates)
    (hInputEmbedding : inputNode.root ≠ embedding) (hUpdatesEmbedding : oldUpdates.root ≠ embedding)
    (hOldSep : regionsDisjoint inputNode.region oldUpdates.region)
    (hHiddenInput : outputStatus = 0 → regionsDisjoint hidden.region inputNode.region)
    (hHiddenUpdates : outputStatus = 0 → regionsDisjoint hidden.region oldUpdates.region)
    (hUpdateInput : regionsDisjoint update.region inputNode.region)
    (hUpdateUpdates : regionsDisjoint update.region oldUpdates.region)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result,
      result.locals[87]? = frame.locals[87]? →
      SelectedFrame params embedding inputNode.root oldUpdates.root
        (statusRoot outputStatus hidden) update.root inputBytes.size oldUpdateBytes.size 0 layer
        hiddenBytes.size updateBytes.size outputStatus result →
      PendingOutput before original ((heap.release oldUpdates).release inputNode)
        ((heap.release oldUpdates).releaseStore (heap.releaseStore initial oldUpdates) inputNode)
        outputStatus hidden update hiddenBytes updateBytes →
      wp «module» rest Q ((heap.release oldUpdates).releaseStore (heap.releaseStore initial oldUpdates) inputNode)
        result env) :
    wp «module» (updatesReleaseCode ++ hiddenReleaseCode ++ rest) Q initial frame env := by
  have hOldNonzero : oldUpdates.root ≠ 0 := by
    intro hZero
    have := hOldUpdates.buffer.rootBound
    rw [hZero] at this
    contradiction
  have hInputNonzero : inputNode.root ≠ 0 := by
    intro hZero
    have := hInput.buffer.rootBound
    rw [hZero] at this
    contradiction
  have hOldHidden : oldUpdates.root ≠ statusRoot outputStatus hidden := by
    by_cases hZero : outputStatus = 0
    · simpa only [statusRoot, hZero, ite_true] using
        hOldUpdates.root_ne (regionsDisjoint_symm (hHiddenUpdates hZero))
    · simpa only [statusRoot, hZero, ite_false] using hOldNonzero
  have hInputHidden : inputNode.root ≠ statusRoot outputStatus hidden := by
    by_cases hZero : outputStatus = 0
    · simpa only [statusRoot, hZero, ite_true] using
        hInput.root_ne (regionsDisjoint_symm (hHiddenInput hZero))
    · simpa only [statusRoot, hZero, ite_false] using hInputNonzero
  have hOldNew := hOldUpdates.root_ne (regionsDisjoint_symm hUpdateUpdates)
  have hInputNew := hInput.root_ne (regionsDisjoint_symm hUpdateInput)
  have hInputOld := hInput.root_ne hOldSep
  have hRead26 : frame.get 26 = some (.i64 oldUpdates.root) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.updatesOwner
  have hRead91 : frame.get 91 = some (.i64 0) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.protectedUpdates
  have hRead82 : frame.get 82 = some (.i64 update.root) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.outputUpdatesOwner
  have hRead88 : frame.get 88 = some (.i64 embedding) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.protectedEmbedding
  have hRead79 : frame.get 79 = some (.i64 (statusRoot outputStatus hidden)) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.outputHiddenOwner
  rw [List.append_assoc]
  unfold updatesReleaseCode
  apply releasePending_spec env original initial before heap params embedding inputNode.root oldUpdates.root
    hidden update inputBytes.size oldUpdateBytes.size 0 layer hiddenBytes updateBytes outputStatus frame
    oldUpdates oldUpdateBytes 26 96
    [(91, 0), (82, update.root), (88, embedding), (79, statusRoot outputStatus hidden)]
    hParams (Or.inr rfl) hMemory hState hOldUpdates hUpdatesFresh hHiddenUpdates hUpdateUpdates hRead26
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact hRead91
    · exact hRead82
    · exact hRead88
    · exact hRead79
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact hOldNonzero
    · exact hOldNew
    · exact hUpdatesEmbedding
    · exact hOldHidden
  intro after hBreak hAfter hAfterMemory
  have hOldRoot32 : oldUpdates.root.toNat ≤ 4294967296 := by
    have := hOldUpdates.buffer.addressBound
    omega
  have hAfterInput := hInput.released oldUpdates hOldUpdates.buffer.rootBound hOldRoot32 hOldSep
  have hAfter26 : after.get 26 = some (.i64 oldUpdates.root) := by
    simpa [Locals.get, hAfter.paramsEq, hParams, hAfter.length] using hAfter.updatesOwner
  have hAfter23 : after.get 23 = some (.i64 inputNode.root) := by
    simpa [Locals.get, hAfter.paramsEq, hParams, hAfter.length] using hAfter.hiddenOwner
  have hAfter91 : after.get 91 = some (.i64 0) := by
    simpa [Locals.get, hAfter.paramsEq, hParams, hAfter.length] using hAfter.protectedUpdates
  have hAfter82 : after.get 82 = some (.i64 update.root) := by
    simpa [Locals.get, hAfter.paramsEq, hParams, hAfter.length] using hAfter.outputUpdatesOwner
  have hAfter88 : after.get 88 = some (.i64 embedding) := by
    simpa [Locals.get, hAfter.paramsEq, hParams, hAfter.length] using hAfter.protectedEmbedding
  have hAfter79 : after.get 79 = some (.i64 (statusRoot outputStatus hidden)) := by
    simpa [Locals.get, hAfter.paramsEq, hParams, hAfter.length] using hAfter.outputHiddenOwner
  unfold hiddenReleaseCode
  apply releasePending_spec env original (heap.releaseStore initial oldUpdates) before (heap.release oldUpdates)
    params embedding inputNode.root oldUpdates.root hidden update inputBytes.size oldUpdateBytes.size
    0 layer hiddenBytes updateBytes outputStatus after inputNode inputBytes 23 96
    [(26, oldUpdates.root), (91, 0), (82, update.root), (88, embedding), (79, statusRoot outputStatus hidden)]
    hParams (Or.inr rfl) hAfterMemory hAfter hAfterInput hInputFresh hHiddenInput hUpdateInput hAfter23
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact hAfter26
    · exact hAfter91
    · exact hAfter82
    · exact hAfter88
    · exact hAfter79
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact hInputOld
    · exact hInputNonzero
    · exact hInputNew
    · exact hInputEmbedding
    · exact hInputHidden
  intro result hResultBreak hResult hFinal
  exact hNext result (hResultBreak.trans hBreak) hResult hFinal

#print axioms oldRelease_owned_spec
end Project.Gpt2QuantizedCached.CachedHidden
