import Project.Gpt2QuantizedCached.CachedHidden.FinishPrepare

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.ProofKit PackedFloatFrame

structure ResultFrame (params : List Value) (embedding updates : UInt64)
    (status hidden cache : UInt64) (hiddenSize cacheSize : Nat) (frame : Locals) : Prop where
  paramsEq : frame.params = params
  length : frame.locals.length = 144
  values : frame.values = []
  typed : I64Values frame.locals
  embeddingOwner : frame.locals[5]? = some (.i64 embedding)
  updatesOwner : frame.locals[92]? = some (.i64 updates)
  updatesPtr : frame.locals[93]? = some (.i64 updates)
  status : frame.locals[112]? = some (.i64 status)
  hiddenOwner : frame.locals[113]? = some (.i64 hidden)
  hiddenPtr : frame.locals[114]? = some (.i64 hidden)
  hiddenSize : frame.locals[115]? = some (.i64 (UInt64.ofNat hiddenSize))
  cacheOwner : frame.locals[116]? = some (.i64 cache)
  cachePtr : frame.locals[117]? = some (.i64 cache)
  cacheSize : frame.locals[118]? = some (.i64 (UInt64.ofNat cacheSize))

def finishFailureCode : Program :=
  [.localGet 114, .localSet 120,
   .constI64 0, .localSet 121, .constI64 0, .localSet 122, .constI64 0, .localSet 123,
   .constI64 0, .localSet 124, .constI64 0, .localSet 125, .constI64 0, .localSet 126]

def finishSuccessCode : Program := (Annotation.resolve func58 [⟨107, .elseBranch⟩]).getD []

theorem emitted_finishBranch : (func58.drop 107).take 1 = [.iff 0 0 finishFailureCode finishSuccessCode] := rfl

theorem finishFailure_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (embedding hidden updates : UInt64) (hiddenSize updatesSize : Nat) (status : UInt64) (frame : Locals)
    (hParams : params.length = 8)
    (hState : FinishFrame params embedding hidden updates hiddenSize updatesSize status frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, ResultFrame params embedding updates status 0 0 0 0 result →
      wp «module» rest Q store result env) :
    wp «module» (finishFailureCode ++ rest) Q store frame env := by
  simp only [finishFailureCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, hParams, hState.length, hState.values, hState.status]
  apply hNext
  constructor <;>
    simp (config := { maxDischargeDepth := 64 }) only [hState.length, List.length_set,
      List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte, I64Values.set,
      hState.typed, hState.embeddingOwner, hState.updatesOwner, hState.updatesPtr,
      show UInt64.ofNat 0 = 0 from rfl]

#print axioms finishFailure_spec
end Project.Gpt2QuantizedCached.CachedHidden
