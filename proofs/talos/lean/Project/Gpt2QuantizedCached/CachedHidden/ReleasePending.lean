import Project.Gpt2QuantizedCached.CachedHidden.PendingOutput
import Project.Gpt2QuantizedCached.CachedHidden.LayerRelease

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem releasePending_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (params : List Value) (embedding input oldUpdates : UInt64) (hidden update : FreeNode)
    (inputSize updateSize : Nat) (status : UInt64) (layer : Nat)
    (hiddenBytes updateBytes : ByteArray) (outputStatus : UInt64) (frame : Locals)
    (node : FreeNode) (bytes : ByteArray) (ownerLocal scratch : Nat) (retained : List (Nat × UInt64))
    (hParams : params.length = 8) (hScratch : scratch = 87 ∨ scratch = 96)
    (hMemory : PendingOutput before original heap initial outputStatus hidden update hiddenBytes updateBytes)
    (hState : SelectedFrame params embedding input oldUpdates (statusRoot outputStatus hidden) update.root
      inputSize updateSize status layer hiddenBytes.size updateBytes.size outputStatus frame)
    (hOwner : heap.OwnsPacked initial node bytes) (hFresh : before.FreshNode node)
    (hHiddenSep : outputStatus = 0 → regionsDisjoint hidden.region node.region)
    (hUpdatesSep : regionsDisjoint update.region node.region)
    (hRead : frame.get ownerLocal = some (.i64 node.root))
    (hRetained : ∀ entry ∈ retained, frame.get entry.1 = some (.i64 entry.2))
    (hNe : ∀ entry ∈ retained, node.root ≠ entry.2)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result,
      result.locals[87]? = frame.locals[87]? →
      SelectedFrame params embedding input oldUpdates (statusRoot outputStatus hidden) update.root
        inputSize updateSize status layer hiddenBytes.size updateBytes.size outputStatus result →
      PendingOutput before original (heap.release node) (heap.releaseStore initial node)
        outputStatus hidden update hiddenBytes updateBytes →
      wp «module» rest Q (heap.releaseStore initial node) result env) :
    wp «module» (PackedReleaseFilter.program ownerLocal (retained.map Prod.fst)
      (PackedReleaseCounted.program ownerLocal scratch 65) ++ rest) Q initial frame env := by
  have hNonzero : node.root ≠ 0 := by
    intro hZero
    have := hOwner.buffer.rootBound
    rw [hZero] at this
    contradiction
  have hEnabled := (PackedReleaseCounted.enabled_iff node.root retained).mpr ⟨hNonzero, hNe⟩
  apply selectedRelease_spec env initial heap params embedding input oldUpdates
    (statusRoot outputStatus hidden) update.root inputSize updateSize status layer
    hiddenBytes.size updateBytes.size outputStatus frame node bytes node.root ownerLocal scratch retained
    hParams hScratch hMemory.heapAt (fun _ => ⟨rfl, hOwner⟩) hState hRead hRetained
  intro hSelected hHeap
  simp only [PackedReleaseCounted.filteredFrame, PackedReleaseCounted.filteredHeap,
    PackedReleaseCounted.filteredStore, hEnabled, ite_true] at hSelected hHeap ⊢
  apply hNext _ ?_ hSelected (hMemory.released node bytes hOwner hFresh hHiddenSep hUpdatesSep hHeap)
  rcases hScratch with rfl | rfl <;>
    simp only [FixedArrayCapacity.capacityFrame, hState.paramsEq, hParams, Nat.reduceSub,
      List.getElem?_set, Nat.reduceEqDiff, reduceIte]

#print axioms releasePending_spec
end Project.Gpt2QuantizedCached.CachedHidden
