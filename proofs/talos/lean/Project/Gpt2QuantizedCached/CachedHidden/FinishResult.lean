import Project.Gpt2QuantizedCached.CachedHidden.FinishPrepare

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.ProofKit PackedFloatFrame

structure ResultFrame (params : List Value) (embedding updates : UInt64)
    (status hidden cache : UInt64) (hiddenSize cacheSize : Nat) (frame : Locals) : Prop where
  paramsEq : frame.params = params
  length : frame.locals.length = 141
  values : frame.values = []
  typed : I64Values frame.locals
  embeddingOwner : frame.locals[5]? = some (.i64 embedding)
  updatesOwner : frame.locals[83]? = some (.i64 updates)
  updatesPtr : frame.locals[84]? = some (.i64 updates)
  status : frame.locals[103]? = some (.i64 status)
  hiddenOwner : frame.locals[104]? = some (.i64 hidden)
  hiddenPtr : frame.locals[105]? = some (.i64 hidden)
  hiddenSize : frame.locals[106]? = some (.i64 (UInt64.ofNat hiddenSize))
  cacheOwner : frame.locals[107]? = some (.i64 cache)
  cachePtr : frame.locals[108]? = some (.i64 cache)
  cacheSize : frame.locals[109]? = some (.i64 (UInt64.ofNat cacheSize))

def finishFailureCode : Program :=
  [.localGet 105, .localSet 111,
   .constI64 0, .localSet 112, .constI64 0, .localSet 113, .constI64 0, .localSet 114,
   .constI64 0, .localSet 115, .constI64 0, .localSet 116, .constI64 0, .localSet 117]

def finishSuccessCode : Program := (Annotation.resolve func58 [⟨105, .elseBranch⟩]).getD []

theorem emitted_finishBranch : (func58.drop 105).take 1 = [.iff 0 0 finishFailureCode finishSuccessCode] := rfl

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
