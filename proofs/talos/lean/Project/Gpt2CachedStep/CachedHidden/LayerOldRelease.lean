import Project.Gpt2CachedStep.CachedHidden.Code
import Project.Gpt2CachedStep.Release
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

def oldReleaseHeap (heap : Heap) (input updates : FreeNode) (layer : Nat) : Heap :=
  if layer = 0 then heap else (heap.release updates).release input

def oldReleaseStore (heap : Heap) (store : Store Unit) (input updates : FreeNode) (layer : Nat) : Store Unit :=
  if layer = 0 then store else (heap.release updates).releaseStore (heap.releaseStore store updates) input

def oldReleaseCode : Wasm.Program :=
  [.localGet 28, .constI64 0, .neI64,
   .localGet 28, .localGet 129, .neI64, .and,
   .localGet 28, .localGet 123, .neI64, .and,
   .localGet 28, .localGet 126, .neI64, .and,
   .localGet 28, .localGet 120, .neI64, .and,
   .iff 0 0 [.localGet 28, .call 42] [],
   .localGet 25, .constI64 0, .neI64,
   .localGet 25, .localGet 28, .neI64, .and,
   .localGet 25, .localGet 129, .neI64, .and,
   .localGet 25, .localGet 123, .neI64, .and,
   .localGet 25, .localGet 126, .neI64, .and,
   .localGet 25, .localGet 120, .neI64, .and,
   .iff 0 0 [.localGet 25, .call 42] []]

set_option maxRecDepth 32768 in
theorem emitted_oldRelease : (layerBody.drop 193).take 44 = oldReleaseCode := rfl

theorem oldRelease_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input updates : FreeNode) (inputBytes updatesBytes : ByteArray) (layer : Nat) (frame : Locals)
    (embedding hidden output : UInt64)
    (hHeap : heap.At initial)
    (hInput : layer ≠ 0 → heap.OwnsPacked initial input inputBytes)
    (hUpdates : layer ≠ 0 → heap.OwnsPacked initial updates updatesBytes)
    (hSeparated : layer ≠ 0 → regionsDisjoint input.region updates.region)
    (hInitial : layer = 0 → input.root = embedding ∧ updates.root = 0)
    (hEmbedding : layer ≠ 0 → input.root ≠ embedding ∧ updates.root ≠ embedding)
    (hHidden : layer ≠ 0 → input.root ≠ hidden ∧ updates.root ≠ hidden)
    (hOutput : layer ≠ 0 → input.root ≠ output ∧ updates.root ≠ output)
    (hValues : frame.values = [])
    (hInitialInput : frame.get 126 = some (.i64 embedding))
    (hInitialUpdates : frame.get 129 = some (.i64 0))
    (hHiddenRead : frame.get 120 = some (.i64 hidden))
    (hOutputRead : frame.get 123 = some (.i64 output))
    (hInputRead : frame.get 25 = some (.i64 input.root))
    (hUpdatesRead : frame.get 28 = some (.i64 updates.root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : (oldReleaseHeap heap input updates layer).At (oldReleaseStore heap initial input updates layer) →
      wp «module» rest Q (oldReleaseStore heap initial input updates layer) frame env) :
    wp «module» ((layerBody.drop 193).take 44 ++ rest) Q initial frame env := by
  have hFrame : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hValues.symm
  simp only [Locals.get] at hInitialInput hInitialUpdates hHiddenRead hOutputRead hInputRead hUpdatesRead
  rw [emitted_oldRelease]
  simp only [oldReleaseCode, List.cons_append, List.nil_append]
  by_cases hZero : layer = 0
  · obtain ⟨hInputInitial, hUpdatesInitial⟩ := hInitial hZero
    wp_packed_frame [hValues, hInputRead, hUpdatesRead, hInitialInput, hInitialUpdates,
      hHiddenRead, hOutputRead, hInputInitial, hUpdatesInitial]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simp)]
    wp_packed_frame [hValues, hInputRead, hUpdatesRead, hInitialInput, hInitialUpdates,
      hHiddenRead, hOutputRead, hInputInitial, hUpdatesInitial]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simp)]
    simpa [wp_simp, oldReleaseHeap, oldReleaseStore, hZero, hFrame] using
      hNext (by simpa [oldReleaseHeap, oldReleaseStore, hZero] using hHeap)
  · have hInputOwned := hInput hZero
    have hUpdatesOwned := hUpdates hZero
    have hInputNonzero : input.root ≠ 0 := by
      intro h
      have := hInputOwned.buffer.rootBound
      rw [h] at this
      contradiction
    have hUpdatesNonzero : updates.root ≠ 0 := by
      intro h
      have := hUpdatesOwned.buffer.rootBound
      rw [h] at this
      contradiction
    have hNe := hInputOwned.root_ne (hSeparated hZero)
    have hInputReleased := hInputOwned.released updates hUpdatesOwned.buffer.rootBound
      (by have := hUpdatesOwned.buffer.addressBound; omega) (hSeparated hZero)
    wp_packed_frame [hValues, hUpdatesRead, hInitialUpdates, hInitialInput, hHiddenRead, hOutputRead,
      hUpdatesNonzero, (hEmbedding hZero).2, (hHidden hZero).2, (hOutput hZero).2]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp [hUpdatesNonzero, (hEmbedding hZero).2, (hHidden hZero).2, (hOutput hZero).2])]
    wp_packed_frame [hValues, hUpdatesRead]
    refine wp_call_tw (Release.release_owned env initial heap updates updatesBytes hHeap hUpdatesOwned) ?_
    rintro final values ⟨rfl, rfl, hUpdatesHeap⟩
    wp_packed_frame [hValues, hInputRead, hUpdatesRead, hInitialUpdates, hInitialInput, hHiddenRead, hOutputRead,
      hInputNonzero, hNe, (hEmbedding hZero).1, (hHidden hZero).1, (hOutput hZero).1]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp [hInputNonzero, hNe, (hEmbedding hZero).1, (hHidden hZero).1, (hOutput hZero).1])]
    wp_packed_frame [hValues, hInputRead]
    refine wp_call_tw (Release.release_owned env (heap.releaseStore initial updates) (heap.release updates)
      input inputBytes hUpdatesHeap hInputReleased) ?_
    rintro final values ⟨rfl, rfl, hFinalHeap⟩
    simpa [wp_simp, oldReleaseHeap, oldReleaseStore, hZero, hFrame] using
      hNext (by simpa [oldReleaseHeap, oldReleaseStore, hZero] using hFinalHeap)

#print axioms oldRelease_spec

end Project.Gpt2CachedStep.CachedHidden
