import Project.Gpt2QuantizedCached.CachedHidden.Embedding

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.ProofKit PackedFloatFrame

def finishPrepareCode : Program :=
  [.localGet 23,
   .localSet 88,
   .localGet 24,
   .localSet 89,
   .localGet 25,
   .localSet 90,
   .localGet 26,
   .localSet 91,
   .localGet 27,
   .localSet 92,
   .localGet 28,
   .localSet 93,
   .localGet 29,
   .localSet 94,
   .localGet 88,
   .localSet 95,
   .localGet 89,
   .localSet 96,
   .localGet 90,
   .localSet 97,
   .localGet 92,
   .localSet 99,
   .localGet 93,
   .localSet 100,
   .localGet 94,
   .localSet 101,
   .localGet 99,
   .localSet 103,
   .localGet 100,
   .localSet 104,
   .localGet 101,
   .localSet 105]

theorem emitted_finishPrepare : (func58.drop 58).take 32 = finishPrepareCode := rfl

structure FinishFrame (params : List Value) (embedding hidden updates : UInt64)
    (hiddenSize updatesSize : Nat) (status : UInt64) (frame : Locals) : Prop where
  paramsEq : frame.params = params
  length : frame.locals.length = 141
  values : frame.values = []
  typed : I64Values frame.locals
  embeddingOwner : frame.locals[5]? = some (.i64 embedding)
  updatesOwner : frame.locals[83]? = some (.i64 updates)
  updatesPtr : frame.locals[84]? = some (.i64 updates)
  hiddenOwner : frame.locals[87]? = some (.i64 hidden)
  hiddenPtr : frame.locals[88]? = some (.i64 hidden)
  hiddenSize : frame.locals[89]? = some (.i64 (UInt64.ofNat hiddenSize))
  updateInputPtr : frame.locals[95]? = some (.i64 updates)
  updateInputSize : frame.locals[96]? = some (.i64 (UInt64.ofNat updatesSize))
  status : frame.locals[97]? = some (.i64 status)

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
