import Project.Gpt2QuantizedCached.CachedHidden.LayerControl
import Project.ProofKit.PackedReleaseCounted

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

def cacheReleaseCode : Program :=
  PackedReleaseFilter.program 57 [79, 82] (PackedReleaseCounted.program 57 87 65)

def updatesReleaseCode : Program :=
  PackedReleaseFilter.program 26 [91, 82, 88, 79] (PackedReleaseCounted.program 26 96 65)

def hiddenReleaseCode : Program :=
  PackedReleaseFilter.program 23 [26, 91, 82, 88, 79] (PackedReleaseCounted.program 23 96 65)

theorem emitted_cacheRelease : activeCode.drop 138 = cacheReleaseCode := rfl

theorem emitted_updatesRelease : (layerBody.drop 53).take 9 = updatesReleaseCode := rfl

theorem emitted_hiddenRelease : (layerBody.drop 62).take 10 = hiddenReleaseCode := rfl

theorem AppendedFrame.selected {params : List Value} {embedding input updates hidden cache newUpdates : UInt64}
    {inputSize updatesSize : Nat} {status : UInt64} {layer : Nat}
    {output : LeanExe.Models.Gpt2.Quantized.HiddenResult} {frame : Locals}
    (h : AppendedFrame params embedding input updates hidden cache newUpdates
      inputSize updatesSize status layer output frame) :
    SelectedFrame params embedding input updates hidden newUpdates inputSize updatesSize status
      layer output.hidden.size (updatesSize + output.cache.size) output.status frame :=
  ⟨h.toLayerFrame, h.outputHiddenOwner, h.outputHiddenPtr, h.outputHiddenSize,
   h.outputUpdatesOwner, h.outputUpdatesPtr, h.outputUpdatesSize, h.outputStatus⟩

theorem SelectedFrame.capacityFrame {params : List Value} {embedding input updates hidden newUpdates : UInt64}
    {inputBytes updateBytes : Nat} {inputStatus : UInt64} {layer hiddenBytes newUpdateBytes : Nat}
    {newStatus : UInt64} {frame : Locals}
    (h : SelectedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
      inputStatus layer hiddenBytes newUpdateBytes newStatus frame)
    (hParams : params.length = 8) (scratch : Nat) (value : UInt64) (hScratch : scratch = 87 ∨ scratch = 96) :
    SelectedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
      inputStatus layer hiddenBytes newUpdateBytes newStatus
      (FixedArrayCapacity.capacityFrame frame scratch value) := by
  rcases hScratch with rfl | rfl
  all_goals
    constructor
    · constructor <;>
        simp only [FixedArrayCapacity.capacityFrame, h.paramsEq, hParams, h.length,
          List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
          I64Values.set, h.typed, h.embeddingOwner, h.embeddingPtr, h.embeddingSize,
          h.protectedEmbedding, h.protectedUpdates, h.hiddenOwner, h.hiddenPtr, h.hiddenSize,
          h.updatesOwner, h.updatesPtr, h.updatesSize, h.status, h.counter, h.limit, h.step, h.flag]
    all_goals simp only [FixedArrayCapacity.capacityFrame, h.paramsEq, hParams, h.length,
      List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      h.outputHiddenOwner, h.outputHiddenPtr, h.outputHiddenSize,
      h.outputUpdatesOwner, h.outputUpdatesPtr, h.outputUpdatesSize, h.outputStatus]

theorem SelectedFrame.filtered {params : List Value} {embedding input updates hidden newUpdates : UInt64}
    {inputBytes updateBytes : Nat} {inputStatus : UInt64} {layer hiddenBytes newUpdateBytes : Nat}
    {newStatus : UInt64} {frame : Locals}
    (h : SelectedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
      inputStatus layer hiddenBytes newUpdateBytes newStatus frame)
    (hParams : params.length = 8) (heap : Heap) (owner : UInt64) (retained : List (Nat × UInt64))
    (scratch : Nat) (hScratch : scratch = 87 ∨ scratch = 96) :
    SelectedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
      inputStatus layer hiddenBytes newUpdateBytes newStatus
      (PackedReleaseCounted.filteredFrame heap frame owner retained scratch) := by
  unfold PackedReleaseCounted.filteredFrame
  split
  · exact h.capacityFrame hParams scratch _ hScratch
  · exact h

theorem SelectedFrame.breakFrame {params : List Value} {embedding input updates hidden newUpdates : UInt64}
    {inputBytes updateBytes : Nat} {inputStatus : UInt64} {layer hiddenBytes newUpdateBytes : Nat}
    {newStatus : UInt64} {frame : Locals}
    (h : SelectedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
      inputStatus layer hiddenBytes newUpdateBytes newStatus frame) :
    SelectedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
      inputStatus layer hiddenBytes newUpdateBytes newStatus (CachedHidden.breakFrame frame) := by
  constructor
  · constructor <;>
      simp (config := { maxDischargeDepth := 64 }) only [CachedHidden.breakFrame, h.paramsEq, h.length, List.length_set, List.getElem?_set,
        Nat.reduceEqDiff, Nat.reduceLT, reduceIte, I64Values.set, h.typed,
        h.embeddingOwner, h.embeddingPtr, h.embeddingSize, h.protectedEmbedding,
        h.protectedUpdates, h.hiddenOwner, h.hiddenPtr, h.hiddenSize,
        h.updatesOwner, h.updatesPtr, h.updatesSize, h.status, h.counter, h.limit, h.step, h.flag]
  all_goals simp only [CachedHidden.breakFrame, List.getElem?_set, Nat.reduceEqDiff, reduceIte,
    h.outputHiddenOwner, h.outputHiddenPtr, h.outputHiddenSize,
    h.outputUpdatesOwner, h.outputUpdatesPtr, h.outputUpdatesSize, h.outputStatus]

theorem selectedRelease_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (embedding input updates hidden newUpdates : UInt64)
    (inputBytes updateBytes : Nat) (inputStatus : UInt64) (layer hiddenBytes newUpdateBytes : Nat)
    (newStatus : UInt64) (frame : Locals) (node : FreeNode) (bytes : ByteArray)
    (owner : UInt64) (ownerLocal scratch : Nat) (retained : List (Nat × UInt64))
    (hParams : params.length = 8) (hScratch : scratch = 87 ∨ scratch = 96)
    (hHeap : heap.At initial)
    (hOwner : PackedReleaseCounted.enabled owner retained = true →
      owner = node.root ∧ heap.OwnsPacked initial node bytes)
    (hState : SelectedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
      inputStatus layer hiddenBytes newUpdateBytes newStatus frame)
    (hRead : frame.get ownerLocal = some (.i64 owner))
    (hRetained : ∀ entry ∈ retained, frame.get entry.1 = some (.i64 entry.2))
    (Q : Assertion Unit) (rest : Program)
    (hNext :
      SelectedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
        inputStatus layer hiddenBytes newUpdateBytes newStatus
        (PackedReleaseCounted.filteredFrame heap frame owner retained scratch) →
      (PackedReleaseCounted.filteredHeap heap node owner retained).At
        (PackedReleaseCounted.filteredStore heap initial node owner retained) →
      wp «module» rest Q (PackedReleaseCounted.filteredStore heap initial node owner retained)
        (PackedReleaseCounted.filteredFrame heap frame owner retained scratch) env) :
    wp «module» (PackedReleaseFilter.program ownerLocal (retained.map Prod.fst)
      (PackedReleaseCounted.program ownerLocal scratch 65) ++ rest) Q initial frame env := by
  apply PackedReleaseCounted.filtered_spec env «module» 65 initial heap frame node bytes
    owner ownerLocal scratch retained (typeIdx := some 65) rfl rfl hHeap hOwner hState.values hRead hRetained
  · rw [hState.paramsEq, hParams]
    omega
  · rw [hState.paramsEq, hParams, hState.length]
    omega
  intro hReleased
  exact hNext (hState.filtered hParams heap owner retained scratch hScratch) hReleased

theorem filteredFrame_break (heap : Heap) (frame : Locals) (owner : UInt64)
    (retained : List (Nat × UInt64)) (hParams : frame.params.length = 8) :
    (PackedReleaseCounted.filteredFrame heap frame owner retained 96).locals[87]? = frame.locals[87]? := by
  unfold PackedReleaseCounted.filteredFrame
  split
  · simp only [FixedArrayCapacity.capacityFrame, hParams, Nat.reduceSub,
      List.getElem?_set, Nat.reduceEqDiff, reduceIte]
  · rfl

#print axioms selectedRelease_spec
#print axioms SelectedFrame.filtered
end Project.Gpt2QuantizedCached.CachedHidden
