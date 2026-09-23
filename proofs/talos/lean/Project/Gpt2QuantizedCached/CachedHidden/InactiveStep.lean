import Project.Gpt2QuantizedCached.CachedHidden.Inactive
import Project.Gpt2QuantizedCached.CachedHidden.LayerRelease

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.ProofKit PackedFloatFrame

theorem emitted_layerStep : (layerBody.drop 4).take 116 =
    layerPrepareCode ++ statusTestCode 41 ++ [.iff 0 0 activeCode inactiveCode] ++
    layerBreakCode ++ updatesReleaseCode ++ hiddenReleaseCode ++ layerAdvanceCode := rfl

theorem inactiveTail_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (embedding input updates : UInt64) (inputBytes updateBytes : Nat) (status : UInt64)
    (layer : Nat) (frame : Locals) (hParams : params.length = 8) (hLayer : layer < 12)
    (hState : SelectedFrame params embedding input updates input updates inputBytes updateBytes status
      layer inputBytes updateBytes status frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, LayerFrame params embedding input updates inputBytes updateBytes status
      (layer + 1) result → wp «module» rest Q store result env) :
    wp «module» (layerBreakCode ++ updatesReleaseCode ++ hiddenReleaseCode ++ layerAdvanceCode ++ rest)
      Q store frame env := by
  simp only [List.append_assoc]
  apply layerBreak_spec env store frame status (by rw [hState.paramsEq, hParams]) hState.length
    hState.values hState.status
  have hAfter := hState.breakFrame
  have hRead26 : (breakFrame frame).get 26 = some (.i64 updates) := by
    simpa [Locals.get, hAfter.paramsEq, hParams, hAfter.length] using hAfter.updatesOwner
  have hRead23 : (breakFrame frame).get 23 = some (.i64 input) := by
    simpa [Locals.get, hAfter.paramsEq, hParams, hAfter.length] using hAfter.hiddenOwner
  have hRead91 : (breakFrame frame).get 91 = some (.i64 0) := by
    simpa [Locals.get, hAfter.paramsEq, hParams, hAfter.length] using hAfter.protectedUpdates
  have hRead82 : (breakFrame frame).get 82 = some (.i64 updates) := by
    simpa [Locals.get, hAfter.paramsEq, hParams, hAfter.length] using hAfter.outputUpdatesOwner
  have hRead88 : (breakFrame frame).get 88 = some (.i64 embedding) := by
    simpa [Locals.get, hAfter.paramsEq, hParams, hAfter.length] using hAfter.protectedEmbedding
  have hRead79 : (breakFrame frame).get 79 = some (.i64 input) := by
    simpa [Locals.get, hAfter.paramsEq, hParams, hAfter.length] using hAfter.outputHiddenOwner
  unfold updatesReleaseCode
  apply PackedReleaseFilter.program_spec «module» env store (breakFrame frame) 26 updates
    [(91, 0), (82, updates), (88, embedding), (79, input)]
    (PackedReleaseCounted.program 26 96 65) hAfter.values hRead26
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact hRead91
    · exact hRead82
    · exact hRead88
    · exact hRead79
  · intro hEnabled
    exact False.elim (hEnabled.2 (82, updates) (by simp) rfl)
  intro _
  unfold hiddenReleaseCode
  apply PackedReleaseFilter.program_spec «module» env store (breakFrame frame) 23 input
    [(26, updates), (91, 0), (82, updates), (88, embedding), (79, input)]
    (PackedReleaseCounted.program 23 96 65) hAfter.values hRead23
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact hRead26
    · exact hRead91
    · exact hRead82
    · exact hRead88
    · exact hRead79
  · intro hEnabled
    exact False.elim (hEnabled.2 (79, input) (by simp) rfl)
  intro _
  apply layerAdvance_spec env store (breakFrame frame) params embedding input updates input updates
    inputBytes updateBytes status layer inputBytes updateBytes status hParams hLayer hAfter
    (by simp [breakFrame, hState.length])
  exact hNext

theorem inactiveStep_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (embedding input updates : UInt64) (inputBytes updateBytes : Nat) (status : UInt64)
    (layer : Nat) (frame : Locals) (hParams : params.length = 8) (hLayer : layer < 12)
    (hStatus : status ≠ 0)
    (hState : LayerFrame params embedding input updates inputBytes updateBytes status layer frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, LayerFrame params embedding input updates inputBytes updateBytes status
      (layer + 1) result → wp «module» rest Q store result env) :
    wp «module» ((layerBody.drop 4).take 116 ++ rest) Q store frame env := by
  rw [emitted_layerStep]
  simp only [List.append_assoc]
  apply layerPrepare_spec env store params embedding input updates inputBytes updateBytes status layer frame
    hParams hState
  intro prepared hPrepared
  have hRead : prepared.get 41 = some (.i64 status) := by
    simpa [Locals.get, hPrepared.paramsEq, hParams, hPrepared.length] using hPrepared.statusCopy
  rw [← List.append_assoc (statusTestCode 41) [.iff 0 0 activeCode inactiveCode]]
  apply statusGuard_spec env store prepared 41 status hPrepared.values hRead
  rw [ite_eq_right hStatus]
  have hRun := inactive_spec env store params embedding input updates inputBytes updateBytes status layer
    prepared hParams hPrepared
    (PackedReleaseFilter.afterAction «module» env
      (layerBreakCode ++ (updatesReleaseCode ++ (hiddenReleaseCode ++ (layerAdvanceCode ++ rest)))) Q) []
  apply (List.append_nil inactiveCode) ▸ hRun
  intro selected hSelected
  simp only [wp_nil, PackedReleaseFilter.afterAction]
  have hEmpty : ({ selected with values := [] } : Locals) = selected :=
    Frame.ext _ _ rfl rfl hSelected.values.symm
  rw [hEmpty]
  apply inactiveTail_spec env store params embedding input updates inputBytes updateBytes status layer selected
    hParams hLayer hSelected
  exact hNext

#print axioms inactiveTail_spec
#print axioms inactiveStep_spec
end Project.Gpt2QuantizedCached.CachedHidden
