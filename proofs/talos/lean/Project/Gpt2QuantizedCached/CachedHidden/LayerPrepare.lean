import Project.Gpt2QuantizedCached.CachedHidden.Embedding

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.ProofKit PackedFloatFrame

structure PreparedFrame (params : List Value) (embedding hidden updates : UInt64)
    (inputBytes updateBytes : Nat) (inputStatus : UInt64) (layer : Nat) (frame : Locals) : Prop
    extends LayerFrame params embedding hidden updates inputBytes updateBytes inputStatus layer frame where
  layerCopy : frame.locals[22]? = some (.i64 (UInt64.ofNat layer))
  hiddenOwnerCopy : frame.locals[23]? = some (.i64 (hidden))
  hiddenPtrCopy : frame.locals[24]? = some (.i64 (hidden))
  hiddenSizeCopy : frame.locals[25]? = some (.i64 (UInt64.ofNat inputBytes))
  updatesOriginalCopy : frame.locals[26]? = some (.i64 updates)
  updatesOwnerCopy : frame.locals[30]? = some (.i64 (updates))
  updatesPtrCopy : frame.locals[31]? = some (.i64 (updates))
  updatesSizeCopy : frame.locals[32]? = some (.i64 (UInt64.ofNat updateBytes))
  statusCopy : frame.locals[33]? = some (.i64 (inputStatus))

theorem layerPrepare_spec (env : HostEnv Unit) (initial : Store Unit)
    (params : List Value) (embedding hidden updates : UInt64)
    (hiddenSize updatesSize : Nat) (status : UInt64) (layer : Nat) (frame : Locals)
    (hParams : params.length = 8)
    (hState : LayerFrame params embedding hidden updates hiddenSize updatesSize status layer frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result,
      PreparedFrame params embedding hidden updates hiddenSize updatesSize status layer result →
      wp «module» rest Q initial result env) :
    wp «module» (layerPrepareCode ++ rest) Q initial frame env := by
  simp only [layerPrepareCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, hParams, hState.length, hState.values,
    hState.counter, hState.hiddenOwner, hState.hiddenPtr, hState.hiddenSize,
    hState.updatesOwner, hState.updatesPtr, hState.updatesSize, hState.status]
  apply hNext
  constructor
  · constructor <;>
      simp (config := { maxDischargeDepth := 64 }) only [hState.paramsEq, hState.length,
        List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
        I64Values.set, hState.typed, hState.embeddingOwner, hState.embeddingPtr,
        hState.embeddingSize, hState.protectedEmbedding, hState.protectedUpdates,
        hState.hiddenOwner, hState.hiddenPtr, hState.hiddenSize, hState.updatesOwner,
        hState.updatesPtr, hState.updatesSize, hState.status, hState.counter,
        hState.limit, hState.step]
  all_goals simp only [hState.length, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte]

#print axioms layerPrepare_spec
end Project.Gpt2QuantizedCached.CachedHidden
