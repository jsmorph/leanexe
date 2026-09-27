import Project.Gpt2QuantizedCached.CachedBlock.Attention
import Project.Gpt2QuantizedCached.CachedBlock.Residual
import Project.Gpt2QuantizedCached.CachedBlock.Normalized2
import Project.Gpt2QuantizedCached.CachedBlock.Activated
import Project.Gpt2QuantizedCached.CachedBlock.Projected2
import Project.Gpt2QuantizedCached.CachedBlock.Hidden
import Project.Gpt2QuantizedCached.CachedBlock.Cache
import Project.Gpt2QuantizedCached.CachedBlock.FiniteTest
import Project.ProofKit.PackedReleaseAll

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.ProofKit

def failureCode : Program :=
  [.constI64 4, .localSet 189, .constI64 0, .localSet 190, .constI64 0, .localSet 191,
   .constI64 0, .localSet 192, .constI64 0, .localSet 193, .constI64 0, .localSet 194,
   .constI64 0, .localSet 195]

def releaseCode (owners : List Nat) : Program :=
  owners.flatMap fun owner => PackedReleaseGuard.programTwo owner 190 193 65

def returnCode : Program :=
  [.localGet 189, .localGet 190, .localGet 191, .localGet 192,
   .localGet 193, .localGet 194, .localGet 195]

theorem activatedSuccess_shape : activatedSuccess = projected2Code ++
    [.constI64 0, .localSet 189] ++ hiddenCode ++
    (activatedSuccess.drop 109).take 49 ++ releaseCode [167] := rfl

theorem normalized2Success_shape : normalized2Success = expandedCode ++ activatedCode ++
    finiteTestCode 135 3072 ++ [.iff 0 0 failureCode activatedSuccess] ++ releaseCode [143, 134] := rfl

theorem attentionSuccess_shape : attentionSuccess = projectionCode ++ residualCode ++ normalized2Code ++
    finiteTestCode 102 768 ++ [.iff 0 0 failureCode normalized2Success] ++ releaseCode [110, 95, 83] := rfl

theorem normalizedSuccess_shape : normalizedSuccess = qkvCode ++ attentionCode ++
    finiteTestCode 51 768 ++ [.iff 0 0 failureCode attentionSuccess] ++ releaseCode [59, 45] := rfl

theorem block_shape : func54 = func54.take 19 ++ (func54.drop 19).take 61 ++
    finiteTestCode 13 768 ++ [.iff 0 0 failureCode normalizedSuccess] ++
    releaseCode [21] ++ returnCode := rfl

end Project.Gpt2QuantizedCached.CachedBlock
