import Project.Gpt2QuantizedCached.CachedHidden.PendingOutput
import Project.Gpt2QuantizedCached.CachedHidden.LayerRelease

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem releasePending_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (params : List Value) (embedding input oldUpdates : UInt64) (hidden update : FreeNode)
    (inputSize updateSize : Nat) (status : UInt64) (layer : Nat)
    (hiddenBytes updateBytes : ByteArray) (outputStatus : UInt64) (frame : Locals)
    (node : FreeNode) (bytes : ByteArray) (ownerLocal : Nat) (retained : List (Nat × UInt64))
    (hParams : params.length = 8)
    (hMemory : PendingOutput before original heap initial outputStatus hidden update hiddenBytes updateBytes)
    (hState : StagedFrame params embedding input oldUpdates (statusRoot outputStatus hidden) update.root
      inputSize updateSize status layer hiddenBytes.size updateBytes.size outputStatus frame)
    (hOwner : heap.OwnsPacked initial node bytes) (hFresh : before.FreshNode node)
    (hHiddenSep : outputStatus = 0 → regionsDisjoint hidden.region node.region)
    (hUpdatesSep : regionsDisjoint update.region node.region)
    (hRead : frame.get ownerLocal = some (.i64 node.root))
    (hRetained : ∀ entry ∈ retained, frame.get entry.1 = some (.i64 entry.2))
    (hNe : ∀ entry ∈ retained, node.root ≠ entry.2)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result,
      result.locals[126]? = frame.locals[126]? →
      StagedFrame params embedding input oldUpdates (statusRoot outputStatus hidden) update.root
        inputSize updateSize status layer hiddenBytes.size updateBytes.size outputStatus result →
      PendingOutput before original (heap.release node) (heap.releaseStore initial node)
        outputStatus hidden update hiddenBytes updateBytes →
      wp «module» rest Q (heap.releaseStore initial node) result env) :
    wp «module» (PackedReleaseConjunction.program ownerLocal (retained.map Prod.fst)
      [.localGet ownerLocal, .call 65] ++ rest) Q initial frame env := by
  have hNonzero : node.root ≠ 0 := by
    intro hZero
    have := hOwner.buffer.rootBound
    rw [hZero] at this
    contradiction
  apply PackedReleaseConjunction.program_spec «module» env initial frame ownerLocal node.root retained
    [.localGet ownerLocal, .call 65] hState.values hRead hRetained
  · intro _
    simp only [Locals.get] at hRead
    wp_packed_frame [hState.values, hRead]
    refine wp_call_tw (heap.releasePacked_exact env «module» 65 initial node bytes
      (typeIdx := some 65) rfl rfl hMemory.heapAt hOwner) ?_
    rintro final returned ⟨rfl, rfl, hReleased⟩
    simp only [wp_nil, PackedReleaseFilter.afterAction]
    have hEmpty : ({ frame with values := [] } : Locals) = frame :=
      Frame.ext _ _ rfl rfl hState.values.symm
    rw [hEmpty]
    exact hNext frame rfl hState (hMemory.released node bytes hOwner hFresh hHiddenSep hUpdatesSep hReleased)
  · intro hSkip
    exact False.elim (hSkip ⟨hNonzero, hNe⟩)

#print axioms releasePending_spec
end Project.Gpt2QuantizedCached.CachedHidden
