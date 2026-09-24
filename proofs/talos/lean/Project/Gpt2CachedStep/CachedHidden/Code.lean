import Project.Gpt2CachedStep.Program
import Project.ProofKit.Annotation
import Project.ProofKit.PackedAppend

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.ProofKit

def layerBody : Wasm.Program :=
  (Annotation.resolve func36 [⟨77, .block⟩, ⟨0, .loop⟩]).getD []

set_option maxRecDepth 32768 in
theorem emitted_layerLoop : (func36.drop 77).take 1 = [.block 0 0 [.loop 0 0 layerBody]] := rfl

set_option maxRecDepth 32768 in
theorem emitted_layerCopy : (layerBody.drop 127).take 6 =
    PackedCopy.program 106 110 107 112 none ++ PackedCopy.program 108 110 109 112 (some 107) := rfl

set_option maxRecDepth 32768 in
theorem emitted_cacheCopy : (func36.drop 155).take 6 =
    PackedCopy.program 103 107 104 109 none ++ PackedCopy.program 105 107 106 109 (some 104) := rfl

set_option maxRecDepth 32768 in
theorem emitted_layerAppend : (layerBody.drop 94).take 40 = PackedAppend.program 106 := rfl

set_option maxRecDepth 32768 in
theorem emitted_cacheAppend : (func36.drop 122).take 40 = PackedAppend.program 103 := rfl

#print axioms emitted_layerCopy
#print axioms emitted_cacheCopy
#print axioms emitted_layerAppend
#print axioms emitted_cacheAppend

end Project.Gpt2CachedStep.CachedHidden
