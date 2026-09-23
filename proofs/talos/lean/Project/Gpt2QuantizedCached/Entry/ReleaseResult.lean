import Project.Gpt2QuantizedCached.Entry.Release

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

theorem State.get_local {params : List Value} {frame : Locals}
    (h : State params frame) (hParams : params.length = 8)
    (index : Nat) (value : Value) (hIndex : index < 93) (hRead : frame.locals[index]? = some value) :
    frame.get (8 + index) = some value := by
  simp only [Locals.get, h.paramsEq, hParams, h.length,
    show ¬8 + index < 8 by omega, show 8 + index < 8 + 93 by omega, reduceIte,
    Nat.add_sub_cancel_left, hRead]

theorem releaseResult_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (params : List Value) (status : UInt64) (cache logits node : FreeNode)
    (cacheBytes logitsBytes bytes : ByteArray) (frame : Locals) (owner : Nat)
    (hMemory : Completion before original heap initial status cache logits cacheBytes logitsBytes)
    (hNode : heap.OwnsPacked initial node bytes) (hFresh : before.FreshNode node)
    (hCacheSep : status = 0 → regionsDisjoint node.region cache.region)
    (hLogitsSep : status = 0 → regionsDisjoint node.region logits.region)
    (hParams : params.length = 8)
    (hState : ResultState params status (statusRoot status cache) (statusRoot status logits)
      cacheBytes.size logitsBytes.size frame)
    (hRead : frame.get owner = some (.i64 node.root))
    (Q : Assertion Unit) (rest : Program)
    (hNext : Completion before original (heap.release node) (heap.releaseStore initial node)
      status cache logits cacheBytes logitsBytes → wp «module» rest Q (heap.releaseStore initial node) frame env) :
    wp «module» (releaseCode owner ++ rest) Q initial frame env := by
  change wp «module» (PackedReleaseFilter.program owner [90, 93] [.localGet owner, .call 65] ++ rest) _ _ _ _
  apply release_spec env original initial before heap status cache logits node cacheBytes logitsBytes bytes
    frame owner [(90, statusRoot status cache), (93, statusRoot status logits)] hMemory hNode hFresh
    (fun h => regionsDisjoint_symm (hCacheSep h)) (fun h => regionsDisjoint_symm (hLogitsSep h))
    hState.values hRead
  · intro entry hEntry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hEntry
    rcases hEntry with rfl | rfl
    · exact hState.toState.get_local hParams 82 _ (by decide) hState.cacheOwner
    · exact hState.toState.get_local hParams 85 _ (by decide) hState.logitsOwner
  · intro entry hEntry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hEntry
    rcases hEntry with rfl | rfl
    · exact hNode.root_ne_status status cache hCacheSep
    · exact hNode.root_ne_status status logits hLogitsSep
  · exact hNext

#print axioms releaseResult_spec
end Project.Gpt2QuantizedCached.Entry
