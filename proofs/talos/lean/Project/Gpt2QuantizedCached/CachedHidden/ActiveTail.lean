import Project.Gpt2QuantizedCached.CachedHidden.OldRelease
import Project.Gpt2QuantizedCached.CachedHidden.FirstRelease

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem activeTail_spec (env : HostEnv Unit) (original inputStore initial : Store Unit)
    (before inputHeap heap : Heap) (params : List Value) (embedding inputNode oldUpdates hidden update : FreeNode)
    (embeddingBytes inputBytes oldUpdateBytes hiddenBytes updateBytes : ByteArray) (outputStatus : UInt64)
    (layer : Nat) (frame : Locals) (hParams : params.length = 8) (hLayer : layer < 12)
    (hMemory : PendingOutput inputHeap inputStore heap initial outputStatus hidden update hiddenBytes updateBytes)
    (hBefore : before.Frame original inputHeap inputStore)
    (hCapacity : inputStore.memoryCap «module» 0 = original.memoryCap «module» 0)
    (hEmbedding : before.OwnsPacked original embedding embeddingBytes)
    (hInput : inputHeap.OwnsPacked inputStore inputNode inputBytes)
    (hOldUpdates : layer ≠ 0 → inputHeap.OwnsPacked inputStore oldUpdates oldUpdateBytes)
    (hInputFresh : layer ≠ 0 → before.FreshNode inputNode)
    (hUpdatesFresh : layer ≠ 0 → before.FreshNode oldUpdates)
    (hInputZero : layer = 0 → inputNode.root = embedding.root)
    (hUpdatesZero : layer = 0 → oldUpdates.root = 0)
    (hUpdateSize : oldUpdateBytes.size = layer * 6144)
    (hOldSep : layer ≠ 0 → regionsDisjoint inputNode.region oldUpdates.region)
    (hState : SelectedFrame params embedding.root inputNode.root oldUpdates.root
      (statusRoot outputStatus hidden) update.root inputBytes.size oldUpdateBytes.size 0 layer
      hiddenBytes.size updateBytes.size outputStatus frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      LayerFrame params embedding.root (statusRoot outputStatus hidden) update.root
        hiddenBytes.size updateBytes.size outputStatus (layer + 1) result →
      PendingOutput before original (oldReleasedHeap heap inputNode oldUpdates layer) final
        outputStatus hidden update hiddenBytes updateBytes →
      wp «module» rest Q final result env) :
    wp «module» (layerBreakCode ++ updatesReleaseCode ++ hiddenReleaseCode ++ layerAdvanceCode ++ rest)
      Q initial frame env := by
  have hOutput := hMemory.trans hBefore hCapacity
  have hCurrentInput := hMemory.frame.ownsPacked hMemory.heapAt hInput
  have hCurrentOld (h : layer ≠ 0) := hMemory.frame.ownsPacked hMemory.heapAt (hOldUpdates h)
  have hHiddenInput (h : outputStatus = 0) :=
    (hMemory.hiddenFresh h).owns_disjoint (hMemory.hidden.owned h).buffer.rootBound hInput
  have hHiddenOld (hLayer : layer ≠ 0) (h : outputStatus = 0) :=
    (hMemory.hiddenFresh h).owns_disjoint (hMemory.hidden.owned h).buffer.rootBound (hOldUpdates hLayer)
  have hUpdateInput := hMemory.updatesFresh.owns_disjoint hMemory.updates.buffer.rootBound hInput
  have hUpdateOld (hLayer : layer ≠ 0) :=
    hMemory.updatesFresh.owns_disjoint hMemory.updates.buffer.rootBound (hOldUpdates hLayer)
  simp only [List.append_assoc]
  apply layerBreak_spec env initial frame params embedding.root inputNode.root oldUpdates.root
    (statusRoot outputStatus hidden) update.root inputBytes.size oldUpdateBytes.size 0 layer
    hiddenBytes.size updateBytes.size outputStatus hParams hState
  intro staged hSelected
  rw [← List.append_assoc updatesReleaseCode hiddenReleaseCode]
  by_cases hZero : layer = 0
  · have hFirst : StagedFrame params embedding.root embedding.root 0
        (statusRoot outputStatus hidden) update.root inputBytes.size 0 0 0
        hiddenBytes.size updateBytes.size outputStatus staged := by
      simpa only [hZero, hInputZero hZero, hUpdatesZero hZero, hUpdateSize, Nat.zero_mul] using hSelected
    apply firstRelease_spec env initial params embedding.root (statusRoot outputStatus hidden)
      update.root inputBytes.size hiddenBytes.size updateBytes.size outputStatus staged hParams hFirst
    apply layerAdvance_spec env initial staged params embedding.root inputNode.root oldUpdates.root
      (statusRoot outputStatus hidden) update.root inputBytes.size oldUpdateBytes.size 0 layer
      hiddenBytes.size updateBytes.size outputStatus hParams hLayer hSelected
    intro result hResult
    apply hNext initial result hResult
    simpa only [oldReleasedHeap, hZero, ite_true] using hOutput
  · have hInputEmbedding := hInput.root_ne
      ((hInputFresh hZero).owns_disjoint hInput.buffer.rootBound hEmbedding)
    have hUpdatesEmbedding := (hOldUpdates hZero).root_ne
      ((hUpdatesFresh hZero).owns_disjoint (hOldUpdates hZero).buffer.rootBound hEmbedding)
    apply oldRelease_owned_spec env original initial before heap params embedding.root
      inputNode oldUpdates hidden update inputBytes oldUpdateBytes hiddenBytes updateBytes outputStatus layer
      staged hParams hOutput hSelected hCurrentInput (hCurrentOld hZero)
      (hInputFresh hZero) (hUpdatesFresh hZero) hInputEmbedding hUpdatesEmbedding (hOldSep hZero)
      hHiddenInput (hHiddenOld hZero) hUpdateInput (hUpdateOld hZero)
    intro released hPreservedBreak hReleased hFinal
    apply layerAdvance_spec env _ released params embedding.root inputNode.root oldUpdates.root
      (statusRoot outputStatus hidden) update.root inputBytes.size oldUpdateBytes.size 0 layer
      hiddenBytes.size updateBytes.size outputStatus hParams hLayer hReleased
    intro result hResult
    apply hNext _ result hResult
    simpa only [oldReleasedHeap, hZero, ite_false] using hFinal

#print axioms activeTail_spec
end Project.Gpt2QuantizedCached.CachedHidden
