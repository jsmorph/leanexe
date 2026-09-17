import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function16_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 16
      resolvedFunctions[16]! Cache.raw.codes[16]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function16_valid

theorem function17_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 17
      resolvedFunctions[17]! Cache.raw.codes[17]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function17_valid

theorem function18_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 18
      resolvedFunctions[18]! Cache.raw.codes[18]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function18_valid

theorem function19_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 19
      resolvedFunctions[19]! Cache.raw.codes[19]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function19_valid

end Project.TinyGpt2Hidden.Artifact
