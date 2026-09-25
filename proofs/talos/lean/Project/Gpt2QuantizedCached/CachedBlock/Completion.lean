import Project.Gpt2QuantizedCached.CachedBlock.Shape
import Project.Gpt2QuantizedCached.CachedBlock.StateTransfer

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution
open PackedReleaseMany (Owners Bindings)

theorem memoryCap_eq_fp32 (store : Store Unit) :
    store.memoryCap «module» 0 = store.memoryCap Project.Gpt2CachedStep.«module» 0 := rfl

structure ResultState (params saved : List Value) (bound : Nat) (accepted : Bool)
    (hidden cache : UInt64) (frame : Locals) : Prop where
  paramsEq : frame.params = params
  length : frame.locals.length = 193
  values : frame.values = []
  typed : I64Values frame.locals
  savedEq : frame.locals.take bound = saved
  status : frame.locals[178]? = some (.i64 (if accepted then 0 else 4))
  hiddenOwner : frame.locals[179]? = some (.i64 (if accepted then hidden else 0))
  hiddenPtr : frame.locals[180]? = some (.i64 (if accepted then hidden else 0))
  hiddenSize : frame.locals[181]? = some (.i64 (if accepted then 3072 else 0))
  cacheOwner : frame.locals[182]? = some (.i64 (if accepted then cache else 0))
  cachePtr : frame.locals[183]? = some (.i64 (if accepted then cache else 0))
  cacheSize : frame.locals[184]? = some (.i64 (if accepted then 6144 else 0))

structure Completion (before : Heap) (initial : Store Unit) (heap : Heap) (final : Store Unit)
    (accepted : Bool) (hidden cache : FreeNode) (hiddenBytes cacheBytes : ByteArray) : Prop where
  heapAt : heap.At final
  frame : before.Frame initial heap final
  pages : final.mem.pages ≤ 65536
  memoryCap : final.memoryCap «module» 0 = initial.memoryCap «module» 0
  outputs : accepted = true → heap.OwnsPacked final hidden hiddenBytes ∧
    heap.OwnsPacked final cache cacheBytes
  fresh : accepted = true → before.FreshNode hidden ∧ before.FreshNode cache
  separated : accepted = true → regionsDisjoint hidden.region cache.region

theorem Completion.trans {before middle heap : Heap} {initial intermediate final : Store Unit}
    {accepted : Bool} {hidden cache : FreeNode} {hiddenBytes cacheBytes : ByteArray}
    (h : Completion middle intermediate heap final accepted hidden cache hiddenBytes cacheBytes)
    (hFrame : before.Frame initial middle intermediate)
    (hCap : intermediate.memoryCap «module» 0 = initial.memoryCap «module» 0) :
    Completion before initial heap final accepted hidden cache hiddenBytes cacheBytes := by
  exact ⟨h.heapAt, hFrame.trans h.frame, h.pages, h.memoryCap.trans hCap, h.outputs,
    fun ha => ⟨hFrame.freshNode (h.fresh ha).1, hFrame.freshNode (h.fresh ha).2⟩, h.separated⟩

theorem ResultState.bindings {params saved : List Value} {bound : Nat} {accepted : Bool}
    {hidden cache : UInt64} {before after : Locals} {items : List PackedReleaseMany.Item}
    (h : ResultState params saved bound accepted hidden cache after)
    (hSaved : saved = before.locals.take bound)
    (hBindings : Bindings items before) (hParams : before.params = params)
    (hLength : before.locals.length = 193) (hBound : bound ≤ 193)
    (hIndices : ∀ item ∈ items, item.ownerLocal < params.length + bound) : Bindings items after := by
  exact hBindings.prefix (h.paramsEq.trans hParams.symm) (h.savedEq.trans hSaved)
    (by rw [hLength]; exact hBound) (by rw [h.length]; exact hBound)
    (by simpa only [hParams] using hIndices)

theorem failure_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (params : List Value) (bound : Nat) (hidden cache : UInt64)
    (hParams : frame.params = params) (hParamLength : params.length = 11)
    (hLength : frame.locals.length = 193) (hValues : frame.values = [])
    (hTyped : I64Values frame.locals) (hBound : bound ≤ 178)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, ResultState params (frame.locals.take bound) bound false hidden cache result →
      wp «module» rest Q initial result env) :
    wp «module» (failureCode ++ rest) Q initial frame env := by
  simp only [failureCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hParamLength, hLength, hValues]
  apply hNext
  constructor
  · rfl
  · simp only [List.length_set, hLength]
  · rfl
  · simp (config := { maxDischargeDepth := 16 }) only [I64Values.set, hTyped]
  · simp only [List.take_set_of_le (by omega : bound ≤ 184),
      List.take_set_of_le (by omega : bound ≤ 183), List.take_set_of_le (by omega : bound ≤ 182),
      List.take_set_of_le (by omega : bound ≤ 181), List.take_set_of_le (by omega : bound ≤ 180),
      List.take_set_of_le (by omega : bound ≤ 179), List.take_set_of_le hBound]
  all_goals simp only [List.getElem?_set, List.length_set, hLength, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, Bool.false_eq_true]

#print axioms failure_spec
#print axioms Completion.trans
end Project.Gpt2QuantizedCached.CachedBlock
