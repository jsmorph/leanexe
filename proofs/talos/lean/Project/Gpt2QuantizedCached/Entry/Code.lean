import Project.Gpt2QuantizedCached.Entry.Source
import Project.Gpt2QuantizedCached.CachedHidden.Budget
import Project.Gpt2QuantizedCached.Layout
import Project.Gpt2QuantizedCached.FiniteWords

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.ProofKit

abbrev parameters := CachedHidden.parameters

def inputBody : Program := (Annotation.resolve func59 [⟨21, .elseBranch⟩]).getD []

def cacheBody : Program := (Annotation.resolve func59 [⟨21, .elseBranch⟩, ⟨12, .elseBranch⟩]).getD []

def acceptedBody : Program := (Annotation.resolve func59 [⟨21, .elseBranch⟩, ⟨12, .elseBranch⟩, ⟨34, .elseBranch⟩]).getD []

def hiddenBody : Program := (Annotation.resolve func59 [⟨21, .elseBranch⟩, ⟨12, .elseBranch⟩, ⟨34, .elseBranch⟩, ⟨61, .elseBranch⟩]).getD []

def normalizedBody : Program := (Annotation.resolve func59 [⟨21, .elseBranch⟩, ⟨12, .elseBranch⟩, ⟨34, .elseBranch⟩, ⟨61, .elseBranch⟩, ⟨88, .elseBranch⟩]).getD []

def hiddenCode : Program :=
  [.localGet 0,
   .localSet 16,
   .localGet 1,
   .localSet 17,
   .localGet 2,
   .localSet 18,
   .localGet 3,
   .localSet 19,
   .localGet 4,
   .localSet 20,
   .localGet 5,
   .localSet 21,
   .localGet 6,
   .localSet 22,
   .localGet 7,
   .localSet 23,
   .localGet 16,
   .localGet 17,
   .localGet 18,
   .localGet 19,
   .localGet 20,
   .localGet 21,
   .localGet 22,
   .localGet 23,
   .call 58,
   .localSet 30,
   .localSet 29,
   .localSet 28,
   .localSet 27,
   .localSet 26,
   .localSet 25,
   .localSet 24,
   .localGet 24,
   .localSet 31,
   .localGet 25,
   .localSet 32,
   .localGet 26,
   .localSet 33,
   .localGet 27,
   .localSet 34,
   .localGet 28,
   .localSet 35,
   .localGet 29,
   .localSet 36,
   .localGet 30,
   .localSet 37]

theorem emitted_hidden : acceptedBody.take 46 = hiddenCode := rfl

structure State (params : List Value) (frame : Locals) : Prop where
  paramsEq : frame.params = params
  length : frame.locals.length = 93
  values : frame.values = []
  typed : I64Values frame.locals

structure HiddenState (params : List Value) (status hidden cache : UInt64)
    (hiddenSize cacheSize : Nat) (frame : Locals) : Prop extends State params frame where
  releaseHidden : frame.locals[17]? = some (.i64 hidden)
  releaseCache : frame.locals[20]? = some (.i64 cache)
  status : frame.locals[23]? = some (.i64 status)
  hiddenOwner : frame.locals[24]? = some (.i64 hidden)
  hiddenPtr : frame.locals[25]? = some (.i64 hidden)
  hiddenSize : frame.locals[26]? = some (.i64 (UInt64.ofNat hiddenSize))
  cacheOwner : frame.locals[27]? = some (.i64 cache)
  cachePtr : frame.locals[28]? = some (.i64 cache)
  cacheSize : frame.locals[29]? = some (.i64 (UInt64.ofNat cacheSize))

end Project.Gpt2QuantizedCached.Entry
