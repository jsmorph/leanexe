import Project.Gpt2CachedStep.CachedHidden.LayerLoop

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.ProofKit PackedFloatFrame

def CachePreparedState (params : List Value) (embeddingPtr hiddenPtr updatesPtr cachePtr : UInt64)
    (cacheSize updatesSize : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 119 ∧ frame.values = [] ∧ I64Values frame.locals ∧
  frame.locals[11]? = some (.i64 embeddingPtr) ∧ frame.locals[75]? = some (.i64 updatesPtr) ∧
  frame.locals[89]? = some (.i64 hiddenPtr) ∧ frame.locals[90]? = some (.i64 hiddenPtr) ∧
  frame.locals[91]? = some (.i64 3072) ∧
  frame.locals[85]? = some (.i64 (UInt64.ofNat cacheSize)) ∧
  frame.locals[87]? = some (.i64 (UInt64.ofNat updatesSize)) ∧
  frame.locals[95]? = some (.i64 cachePtr) ∧ frame.locals[96]? = some (.i64 (UInt64.ofNat cacheSize)) ∧
  frame.locals[97]? = some (.i64 updatesPtr) ∧ frame.locals[98]? = some (.i64 (UInt64.ofNat updatesSize))

def cachePrepareCode : Wasm.Program :=
  [.localGet 25, .localSet 80, .localGet 26, .localSet 81, .localGet 27, .localSet 82,
   .localGet 28, .localSet 83, .localGet 29, .localSet 84, .localGet 30, .localSet 85,
   .localGet 80, .localSet 86, .localGet 81, .localSet 87, .localGet 82, .localSet 88,
   .localGet 84, .localSet 90, .localGet 85, .localSet 91,
   .localGet 86, .localSet 97, .localGet 87, .localSet 98, .localGet 88, .localSet 99,
   .localGet 4, .localSet 92, .localGet 5, .localSet 93,
   .localGet 90, .localSet 94, .localGet 91, .localSet 95,
   .localGet 92, .localSet 103, .localGet 93, .localSet 104,
   .localGet 94, .localSet 105, .localGet 95, .localSet 106]

set_option maxRecDepth 32768 in
theorem emitted_cachePrepare : (func36.drop 76).take 44 = cachePrepareCode := rfl

theorem cachePrepare_spec (env : HostEnv Unit) (store : Store Unit)
    (weightsOwner weightsPtr cacheOwner cachePtr embeddingPtr hiddenPtr updatesPtr : UInt64)
    (weights cache : ByteArray) (token : UInt32) (position updatesSize : Nat) (frame : Locals)
    (hState : LayerState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      embeddingPtr hiddenPtr updatesPtr 12 updatesSize frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, CachePreparedState
      (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      embeddingPtr hiddenPtr updatesPtr cachePtr cache.size updatesSize result → wp «module» rest Q store result env) :
    wp «module» ((func36.drop 76).take 44 ++ rest) Q store frame env := by
  rcases hState with ⟨hParams, hLocals, hValues, hTyped, hEmbedding, _, _, hInputOwner, hInputPtr, hInputSize,
    hUpdatesOwner, hUpdatesPtr, hUpdatesSize, _, _, _, _⟩
  rw [emitted_cachePrepare]
  simp only [cachePrepareCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hInputOwner, hInputPtr, hInputSize,
    hUpdatesOwner, hUpdatesPtr, hUpdatesSize]
  apply hNext
  simp (config := { maxDischargeDepth := 64 }) only [CachePreparedState, parameters, hLocals,
    List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
    I64Values.set, hTyped, hEmbedding, UInt64.ofNat_uInt32ToNat, and_self]

#print axioms cachePrepare_spec

end Project.Gpt2CachedStep.CachedHidden
