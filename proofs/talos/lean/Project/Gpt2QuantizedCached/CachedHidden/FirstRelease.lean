import Project.Gpt2QuantizedCached.CachedHidden.LayerRelease

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.ProofKit

theorem firstRelease_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (embedding hidden newUpdates : UInt64) (inputSize hiddenSize updatesSize : Nat)
    (outputStatus : UInt64) (frame : Locals) (hParams : params.length = 8)
    (hState : StagedFrame params embedding embedding 0 hidden newUpdates inputSize 0 0 0
      hiddenSize updatesSize outputStatus frame)
    (Q : Assertion Unit) (rest : Program) (hNext : wp «module» rest Q store frame env) :
    wp «module» (updatesReleaseCode ++ hiddenReleaseCode ++ rest) Q store frame env := by
  have hRead26 : frame.get 26 = some (.i64 0) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.updatesOwner
  have hRead23 : frame.get 23 = some (.i64 embedding) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.hiddenOwner
  have hRead91 : frame.get 145 = some (.i64 0) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.protectedUpdates
  have hRead82 : frame.get 138 = some (.i64 newUpdates) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.nextUpdatesOwner
  have hRead88 : frame.get 142 = some (.i64 embedding) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.protectedEmbedding
  have hRead79 : frame.get 135 = some (.i64 hidden) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.nextHiddenOwner
  rw [List.append_assoc]
  unfold updatesReleaseCode
  apply PackedReleaseConjunction.program_spec «module» env store frame 26 0
    [(145, 0), (138, newUpdates), (142, embedding), (135, hidden)]
    [.localGet 26, .call 65] hState.values hRead26
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact hRead91
    · exact hRead82
    · exact hRead88
    · exact hRead79
  · intro hEnabled
    exact False.elim (hEnabled.1 rfl)
  intro _
  unfold hiddenReleaseCode
  apply PackedReleaseConjunction.program_spec «module» env store frame 23 embedding
    [(26, 0), (145, 0), (138, newUpdates), (142, embedding), (135, hidden)]
    [.localGet 23, .call 65] hState.values hRead23
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact hRead26
    · exact hRead91
    · exact hRead82
    · exact hRead88
    · exact hRead79
  · intro hEnabled
    exact False.elim (hEnabled.2 (142, embedding) (by simp) rfl)
  intro _
  exact hNext

#print axioms firstRelease_spec
end Project.Gpt2QuantizedCached.CachedHidden
