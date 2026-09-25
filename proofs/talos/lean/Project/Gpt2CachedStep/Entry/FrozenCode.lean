import Project.Gpt2CachedStep.CachedHidden.FrozenSpec
import Project.Gpt2CachedStep.Vocabulary.FrozenSpec
import Project.Gpt2CachedStep.LayerNorm.FrozenFresh

namespace Project.Gpt2CachedStep.Frozen.Entry
open Wasm Project.ProofKit LeanExe.Models.Gpt2

def validBody : Wasm.Program := (Annotation.resolve func38 [⟨25, .elseBranch⟩]).getD []

def parameters (weightsPtr cachePtr : UInt64) (weights cache : ByteArray) (token : UInt32) (position : Nat) : List Value :=
  [.i64 weightsPtr, .i64 (UInt64.ofNat weights.size), .i64 cachePtr,
   .i64 (UInt64.ofNat cache.size), .i64 token.toUInt64, .i64 (UInt64.ofNat position)]

def Valid (weights cache : ByteArray) (token : UInt32) (position : Nat) : Prop :=
  weights.size = parameterWords * 4 ∧ token.toNat < 50257 ∧ position < 128 ∧ cache.size = position * 73728

def State (params : List Value) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 55 ∧ frame.values = [] ∧ I64Values frame.locals

def HiddenState (params : List Value) (hiddenPtr cachePtr : UInt64) (cacheSize : Nat) (frame : Locals) : Prop :=
  State params frame ∧ frame.locals[8]? = some (.i64 hiddenPtr) ∧
  frame.locals[14]? = some (.i64 hiddenPtr) ∧ frame.locals[15]? = some (.i64 hiddenPtr) ∧
  frame.locals[16]? = some (.i64 3072) ∧ frame.locals[17]? = some (.i64 cachePtr) ∧
  frame.locals[18]? = some (.i64 cachePtr) ∧ frame.locals[19]? = some (.i64 (UInt64.ofNat cacheSize))

def NormalizedState (params : List Value) (hiddenPtr cachePtr normalizedPtr : UInt64)
    (cacheSize : Nat) (frame : Locals) : Prop :=
  HiddenState params hiddenPtr cachePtr cacheSize frame ∧
  frame.locals[30]? = some (.i64 normalizedPtr) ∧ frame.locals[33]? = some (.i64 normalizedPtr) ∧
  frame.locals[34]? = some (.i64 normalizedPtr) ∧ frame.locals[35]? = some (.i64 3072)

def LogitsState (params : List Value) (hiddenPtr normalizedPtr cachePtr logitsPtr : UInt64)
    (cacheSize : Nat) (frame : Locals) : Prop :=
  State params frame ∧ frame.locals[8]? = some (.i64 hiddenPtr) ∧ frame.locals[30]? = some (.i64 normalizedPtr) ∧
  frame.locals[45]? = some (.i64 cachePtr) ∧ frame.locals[46]? = some (.i64 cachePtr) ∧
  frame.locals[47]? = some (.i64 (UInt64.ofNat cacheSize)) ∧ frame.locals[48]? = some (.i64 logitsPtr) ∧
  frame.locals[49]? = some (.i64 logitsPtr) ∧ frame.locals[50]? = some (.i64 201028)

theorem valid_extents {weights cache : ByteArray} {token : UInt32} {position : Nat}
    (h : Valid weights cache token position) :
    4 * (token.toNat * 768 + 768) ≤ weights.size ∧
    4 * (positionOffset + position * 768 + 768) ≤ weights.size ∧
    (blocksOffset + 12 * blockWords) * 4 ≤ weights.size ∧
    position * 12 * 1536 * 4 ≤ cache.size ∧ cache.size + 73728 ≤ 4294967296 := by
  rcases h with ⟨hw, ht, hp, hc⟩
  rw [hw, hc]
  change 4 * (token.toNat * 768 + 768) ≤ 497759232 ∧
    4 * (38597376 + position * 768 + 768) ≤ 497759232 ∧
    497753088 ≤ 497759232 ∧ position * 12 * 1536 * 4 ≤ position * 73728 ∧
    position * 73728 + 73728 ≤ 4294967296
  omega

end Project.Gpt2CachedStep.Frozen.Entry
