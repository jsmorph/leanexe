import Project.Gpt2QuantizedCached.Entry.Logits
import Project.ProofKit.LocalPrefix

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.ProofKit

theorem State.transfer {params : List Value} {before after : Locals}
    (hState : State params before) (hParams : after.params = before.params)
    (hLength : after.locals.length = 93) (hValues : after.values = [])
    (hTyped : I64Values after.locals) : State params after :=
  ⟨hParams.trans hState.paramsEq, hLength, hValues, hTyped⟩

theorem HiddenState.transfer {params : List Value} {status hidden cache : UInt64}
    {hiddenSize cacheSize count : Nat} {before after : Locals}
    (hState : HiddenState params status hidden cache hiddenSize cacheSize before)
    (hParams : after.params = before.params) (hLength : after.locals.length = 93)
    (hValues : after.values = []) (hTyped : I64Values after.locals)
    (hPrefix : after.locals.take count = before.locals.take count) (hCount : 30 ≤ count) :
    HiddenState params status hidden cache hiddenSize cacheSize after := by
  constructor
  · exact hState.toState.transfer hParams hLength hValues hTyped
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.releaseHidden
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.releaseCache
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.status
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.hiddenOwner
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.hiddenPtr
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.hiddenSize
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.cacheOwner
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.cachePtr
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.cacheSize

theorem NormalizedState.transfer {params : List Value} {hidden cache normalized : UInt64}
    {cacheSize count : Nat} {before after : Locals}
    (hState : NormalizedState params hidden cache normalized cacheSize before)
    (hParams : after.params = before.params) (hLength : after.locals.length = 93)
    (hValues : after.values = []) (hTyped : I64Values after.locals)
    (hPrefix : after.locals.take count = before.locals.take count) (hCount : 45 ≤ count) :
    NormalizedState params hidden cache normalized cacheSize after := by
  constructor
  · exact hState.toHiddenState.transfer hParams hLength hValues hTyped hPrefix (by omega)
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.releaseNormalized
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.normalizedOwner
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.normalizedPtr
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.normalizedSize

theorem LogitsState.transfer {params : List Value} {hidden cache normalized logits : UInt64}
    {cacheSize count : Nat} {before after : Locals}
    (hState : LogitsState params hidden cache normalized logits cacheSize before)
    (hParams : after.params = before.params) (hLength : after.locals.length = 93)
    (hValues : after.values = []) (hTyped : I64Values after.locals)
    (hPrefix : after.locals.take count = before.locals.take count) (hCount : 71 ≤ count) :
    LogitsState params hidden cache normalized logits cacheSize after := by
  constructor
  · exact hState.toNormalizedState.transfer hParams hLength hValues hTyped hPrefix (by omega)
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.releaseLogits
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.logitsOwner
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.logitsPtr
  · rw [Frame.local_of_take_eq hPrefix (by omega)]
    exact hState.logitsSize

#print axioms HiddenState.transfer
#print axioms NormalizedState.transfer
#print axioms LogitsState.transfer
end Project.Gpt2QuantizedCached.Entry
