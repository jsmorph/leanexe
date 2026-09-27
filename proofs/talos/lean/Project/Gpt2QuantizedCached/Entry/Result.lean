import Project.Gpt2QuantizedCached.Entry.Logits
import Project.ProofKit.LocalPrefix

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.ProofKit PackedFloatFrame

structure ResultState (params : List Value) (status cache logits : UInt64)
    (cacheSize logitsSize : Nat) (frame : Locals) : Prop extends State params frame where
  status : frame.locals[81]? = some (.i64 status)
  cacheOwner : frame.locals[82]? = some (.i64 cache)
  cachePtr : frame.locals[83]? = some (.i64 cache)
  cacheSize : frame.locals[84]? = some (.i64 (UInt64.ofNat cacheSize))
  logitsOwner : frame.locals[85]? = some (.i64 logits)
  logitsPtr : frame.locals[86]? = some (.i64 logits)
  logitsSize : frame.locals[87]? = some (.i64 (UInt64.ofNat logitsSize))

def failureResultCode (statusCode : Instruction) : Program :=
  [statusCode, .localSet 89,
   .constI64 0, .localSet 90, .constI64 0, .localSet 91, .constI64 0, .localSet 92,
   .constI64 0, .localSet 93, .constI64 0, .localSet 94, .constI64 0, .localSet 95]

def successResultCode : Program :=
  [.constI64 0, .localSet 89,
   .localGet 35, .localSet 90, .localGet 36, .localSet 91, .localGet 37, .localSet 92,
   .localGet 76, .localSet 93, .localGet 77, .localSet 94, .localGet 78, .localSet 95]

def returnCode : Program :=
  [.localGet 89, .localGet 90, .localGet 91, .localGet 92, .localGet 93, .localGet 94, .localGet 95]

theorem emitted_return : func59.drop 22 = returnCode := rfl

theorem failureResult_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (status : UInt64) (statusCode : Instruction) (frame : Locals)
    (hParams : params.length = 8) (hState : State params frame)
    (hStatusCode : statusCode = .constI64 status ∨
      (statusCode = .localGet 31 ∧ frame.locals[23]? = some (.i64 status)))
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, ResultState params status 0 0 0 0 result →
      result.locals.take 81 = frame.locals.take 81 → wp «module» rest Q store result env) :
    wp «module» (failureResultCode statusCode ++ rest) Q store frame env := by
  rcases hStatusCode with rfl | ⟨rfl, hStatus⟩
  all_goals
    simp only [failureResultCode, List.cons_append, List.nil_append]
    first
    | wp_packed_frame [hState.paramsEq, hParams, hState.length, hState.values, hStatus]
    | wp_packed_frame [hState.paramsEq, hParams, hState.length, hState.values]
    apply hNext
    · constructor
      · constructor <;> simp (config := { maxDischargeDepth := 32 }) only [hState.paramsEq,
          hState.length, List.length_set, I64Values.set, hState.typed]
      all_goals simp only [hState.length, List.length_set, List.getElem?_set, Nat.reduceEqDiff,
        Nat.reduceLT, reduceIte, show UInt64.ofNat 0 = 0 from rfl]
    · simp only [List.take_set_of_le, Nat.reduceLeDiff]

theorem successResult_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (hidden cache normalized logits : UInt64) (cacheSize : Nat) (frame : Locals)
    (hParams : params.length = 8)
    (hState : LogitsState params hidden cache normalized logits cacheSize frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, ResultState params 0 cache logits cacheSize 201028 result →
      result.locals.take 81 = frame.locals.take 81 → wp «module» rest Q store result env) :
    wp «module» (successResultCode ++ rest) Q store frame env := by
  simp only [successResultCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, hParams, hState.length, hState.values,
    hState.cacheOwner, hState.cachePtr, hState.cacheSize, hState.logitsOwner, hState.logitsPtr, hState.logitsSize]
  apply hNext
  · constructor
    · constructor <;> simp (config := { maxDischargeDepth := 32 }) only [hState.paramsEq,
        hState.length, List.length_set, I64Values.set, hState.typed]
    all_goals simp only [hState.length, List.length_set, List.getElem?_set, Nat.reduceEqDiff,
      Nat.reduceLT, reduceIte, show UInt64.ofNat 201028 = 201028 from rfl]
  · simp only [List.take_set_of_le, Nat.reduceLeDiff]

theorem return_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (status cache logits : UInt64) (cacheSize logitsSize : Nat) (frame : Locals)
    (hParams : params.length = 8) (hState : ResultState params status cache logits cacheSize logitsSize frame)
    (Q : Assertion Unit) (hNext : Q (.Fallthrough store { frame with values :=
      [.i64 (UInt64.ofNat logitsSize), .i64 logits, .i64 logits,
       .i64 (UInt64.ofNat cacheSize), .i64 cache, .i64 cache, .i64 status] })) :
    wp «module» returnCode Q store frame env := by
  unfold returnCode
  wp_packed_frame [hState.paramsEq, hParams, hState.length, hState.values,
    hState.status, hState.cacheOwner, hState.cachePtr, hState.cacheSize,
    hState.logitsOwner, hState.logitsPtr, hState.logitsSize]
  simpa only [hState.paramsEq] using hNext

#print axioms failureResult_spec
#print axioms successResult_spec
#print axioms return_spec
end Project.Gpt2QuantizedCached.Entry
