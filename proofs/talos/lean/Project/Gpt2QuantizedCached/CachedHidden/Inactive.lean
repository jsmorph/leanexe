import Project.Gpt2QuantizedCached.CachedHidden.LayerControl

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.ProofKit PackedFloatFrame

def inactiveCode : Program :=
  [.localGet 31, .localSet 79, .localGet 32, .localSet 80,
   .localGet 33, .localSet 81, .localGet 38, .localSet 82,
   .localGet 39, .localSet 83, .localGet 40, .localSet 84,
   .localGet 41, .localSet 85]

theorem emitted_layerBranch : (layerBody.drop 28).take 11 =
    statusTestCode 41 ++ [.iff 0 0 activeCode inactiveCode] := rfl

theorem inactive_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (embedding input updates : UInt64) (inputBytes updateBytes : Nat) (status : UInt64)
    (layer : Nat) (frame : Locals) (hParams : params.length = 8)
    (hState : PreparedFrame params embedding input updates inputBytes updateBytes status layer frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result,
      SelectedFrame params embedding input updates input updates inputBytes updateBytes status
        layer inputBytes updateBytes status result → wp «module» rest Q store result env) :
    wp «module» (inactiveCode ++ rest) Q store frame env := by
  simp only [inactiveCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, hParams, hState.length, hState.values,
    hState.hiddenOwnerCopy, hState.hiddenPtrCopy, hState.hiddenSizeCopy,
    hState.updatesOwnerCopy, hState.updatesPtrCopy, hState.updatesSizeCopy, hState.statusCopy]
  apply hNext
  constructor
  · constructor <;>
      simp (config := { maxDischargeDepth := 64 }) only [hState.length, List.length_set, List.getElem?_set, Nat.reduceEqDiff,
        Nat.reduceLT, reduceIte, I64Values.set, hState.typed, hState.embeddingOwner,
        hState.embeddingPtr, hState.embeddingSize, hState.protectedEmbedding,
        hState.protectedUpdates, hState.hiddenOwner, hState.hiddenPtr, hState.hiddenSize,
        hState.updatesOwner, hState.updatesPtr, hState.updatesSize, hState.status,
        hState.counter, hState.limit, hState.step]
  all_goals simp (config := { maxDischargeDepth := 64 }) only [hState.length, List.length_set, List.getElem?_set,
    Nat.reduceEqDiff, Nat.reduceLT, reduceIte]

#print axioms inactive_spec
end Project.Gpt2QuantizedCached.CachedHidden
