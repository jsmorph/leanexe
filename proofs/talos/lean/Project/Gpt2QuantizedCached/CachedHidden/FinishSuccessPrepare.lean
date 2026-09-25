import Project.Gpt2QuantizedCached.CachedHidden.FinishResult

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame

def finishSuccessPrepareCode : Program :=
  [.constI64 0,
   .localSet 111,
   .localGet 95,
   .localSet 112,
   .localGet 96,
   .localSet 113,
   .localGet 97,
   .localSet 114,
   .localGet 4,
   .localSet 106,
   .localGet 5,
   .localSet 107,
   .localGet 103,
   .localSet 108,
   .localGet 104,
   .localSet 109,
   .localGet 106,
   .localSet 118,
   .localGet 107,
   .localSet 119,
   .localGet 108,
   .localSet 120,
   .localGet 109,
   .localSet 121]

def finishSuccessResultCode : Program :=
  [.localSet 115,
   .localGet 115,
   .localSet 116,
   .localGet 107,
   .localGet 109,
   .addI64,
   .localSet 117]

theorem emitted_finishSuccess : finishSuccessCode =
    finishSuccessPrepareCode ++ PackedAppend.program 118 ++ finishSuccessResultCode := rfl

structure SuccessFrame (params : List Value) (embedding hidden updates cache : UInt64)
    (hiddenSize updatesSize cacheSize : Nat) (frame : Locals) : Prop where
  paramsEq : frame.params = params
  length : frame.locals.length = 141
  values : frame.values = []
  typed : I64Values frame.locals
  embeddingOwner : frame.locals[5]? = some (.i64 embedding)
  updatesOwner : frame.locals[83]? = some (.i64 updates)
  updatesPtr : frame.locals[84]? = some (.i64 updates)
  status : frame.locals[103]? = some (.i64 0)
  hiddenOwner : frame.locals[104]? = some (.i64 hidden)
  hiddenPtr : frame.locals[105]? = some (.i64 hidden)
  hiddenSize : frame.locals[106]? = some (.i64 (UInt64.ofNat hiddenSize))
  oldCacheSize : frame.locals[99]? = some (.i64 (UInt64.ofNat cacheSize))
  updateSize : frame.locals[101]? = some (.i64 (UInt64.ofNat updatesSize))
  leftPtr : frame.locals[110]? = some (.i64 cache)
  leftSize : frame.locals[111]? = some (.i64 (UInt64.ofNat cacheSize))
  rightPtr : frame.locals[112]? = some (.i64 updates)
  rightSize : frame.locals[113]? = some (.i64 (UInt64.ofNat updatesSize))

theorem finishSuccessPrepare_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (embedding hidden updates cache : UInt64) (hiddenSize updatesSize cacheSize : Nat) (frame : Locals)
    (hParams : params.length = 8)
    (hCachePtr : params[4]? = some (.i64 cache))
    (hCacheSize : params[5]? = some (.i64 (UInt64.ofNat cacheSize)))
    (hState : FinishFrame params embedding hidden updates hiddenSize updatesSize 0 frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, SuccessFrame params embedding hidden updates cache hiddenSize updatesSize cacheSize result →
      wp «module» rest Q store result env) :
    wp «module» (finishSuccessPrepareCode ++ rest) Q store frame env := by
  simp only [finishSuccessPrepareCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, hParams, hState.length, hState.values,
    hState.hiddenOwner, hState.hiddenPtr, hState.hiddenSize, hState.updateInputPtr,
    hState.updateInputSize, hCachePtr, hCacheSize]
  apply hNext
  constructor <;>
    simp (config := { maxDischargeDepth := 64 }) only [hState.length, List.length_set,
      List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte, I64Values.set,
      hState.typed, hState.embeddingOwner, hState.updatesOwner, hState.updatesPtr]

#print axioms finishSuccessPrepare_spec
end Project.Gpt2QuantizedCached.CachedHidden
