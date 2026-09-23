import Project.Gpt2QuantizedCached.CachedHidden.Embedding

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.ProofKit PackedFloatFrame

def finishPrepareCode : Program :=
  [.localGet 23,
   .localSet 97,
   .localGet 24,
   .localSet 98,
   .localGet 25,
   .localSet 99,
   .localGet 26,
   .localSet 100,
   .localGet 27,
   .localSet 101,
   .localGet 28,
   .localSet 102,
   .localGet 29,
   .localSet 103,
   .localGet 97,
   .localSet 104,
   .localGet 98,
   .localSet 105,
   .localGet 99,
   .localSet 106,
   .localGet 101,
   .localSet 108,
   .localGet 102,
   .localSet 109,
   .localGet 103,
   .localSet 110,
   .localGet 108,
   .localSet 112,
   .localGet 109,
   .localSet 113,
   .localGet 110,
   .localSet 114]

theorem emitted_finishPrepare : (func58.drop 60).take 32 = finishPrepareCode := rfl

structure FinishFrame (params : List Value) (embedding hidden updates : UInt64)
    (hiddenSize updatesSize : Nat) (status : UInt64) (frame : Locals) : Prop where
  paramsEq : frame.params = params
  length : frame.locals.length = 144
  values : frame.values = []
  typed : I64Values frame.locals
  embeddingOwner : frame.locals[5]? = some (.i64 embedding)
  updatesOwner : frame.locals[92]? = some (.i64 updates)
  updatesPtr : frame.locals[93]? = some (.i64 updates)
  hiddenOwner : frame.locals[96]? = some (.i64 hidden)
  hiddenPtr : frame.locals[97]? = some (.i64 hidden)
  hiddenSize : frame.locals[98]? = some (.i64 (UInt64.ofNat hiddenSize))
  updateInputPtr : frame.locals[104]? = some (.i64 updates)
  updateInputSize : frame.locals[105]? = some (.i64 (UInt64.ofNat updatesSize))
  status : frame.locals[106]? = some (.i64 status)

theorem finishPrepare_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (embedding hidden updates : UInt64) (hiddenSize updatesSize : Nat) (status : UInt64) (frame : Locals)
    (hParams : params.length = 8)
    (hState : LayerFrame params embedding hidden updates hiddenSize updatesSize status 12 frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, FinishFrame params embedding hidden updates hiddenSize updatesSize status result →
      wp «module» rest Q store result env) :
    wp «module» (finishPrepareCode ++ rest) Q store frame env := by
  simp only [finishPrepareCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, hParams, hState.length, hState.values,
    hState.hiddenOwner, hState.hiddenPtr, hState.hiddenSize, hState.updatesOwner,
    hState.updatesPtr, hState.updatesSize, hState.status]
  apply hNext
  constructor <;>
    simp (config := { maxDischargeDepth := 64 }) only [hState.length, List.length_set,
      List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hState.typed, hState.embeddingOwner]

#print axioms finishPrepare_spec
end Project.Gpt2QuantizedCached.CachedHidden
