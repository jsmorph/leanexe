import Project.Gpt2QuantizedCached.Entry.NormalizedStage

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

theorem releaseNullResult_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (status : UInt64) (owner : Nat) (frame : Locals) (hParams : params.length = 8)
    (hState : ResultState params status 0 0 0 0 frame)
    (hRead : frame.get owner = some (.i64 0)) (Q : Assertion Unit) (rest : Program)
    (hNext : wp «module» rest Q store frame env) :
    wp «module» (releaseCode owner ++ rest) Q store frame env := by
  change wp «module» (PackedReleaseFilter.program owner [90, 93] [.localGet owner, .call 65] ++ rest) _ _ _ _
  apply PackedReleaseFilter.program_spec «module» env store frame owner 0 [(90, 0), (93, 0)]
    [.localGet owner, .call 65] hState.values hRead
  · intro entry hEntry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hEntry
    rcases hEntry with rfl | rfl
    · exact hState.toState.get_local hParams 82 _ (by decide) hState.cacheOwner
    · exact hState.toState.get_local hParams 85 _ (by decide) hState.logitsOwner
  · intro hActive
    exact False.elim (hActive.1 rfl)
  · intro _
    exact hNext

theorem failureHidden_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (status : UInt64) (frame : Locals) (hParams : params.length = 8)
    (hState : HiddenState params status 0 0 0 0 frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, ResultState params status 0 0 0 0 result →
      result.locals[17]? = some (.i64 0) → wp «module» rest Q store result env) :
    wp «module» (hiddenFailureCode ++ rest) Q store frame env := by
  simp only [hiddenFailureCode, List.append_assoc]
  apply failureResult_spec env store params status (.localGet 31) frame hParams hState.toState
    (Or.inr ⟨rfl, hState.status⟩)
  intro result hResult hPrefix
  apply releaseNullResult_spec env store params status 28 result hParams hResult
    (hResult.toState.get_local hParams 20 _ (by decide)
      ((Frame.local_of_take_eq hPrefix (by decide)).trans hState.releaseCache))
  exact hNext result hResult ((Frame.local_of_take_eq hPrefix (by decide)).trans hState.releaseHidden)

#print axioms releaseNullResult_spec
#print axioms failureHidden_spec
end Project.Gpt2QuantizedCached.Entry
