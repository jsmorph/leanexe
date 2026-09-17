import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function32_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 32
      resolvedFunctions[32]! Cache.raw.codes[32]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function32_valid

theorem function33_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 33
      resolvedFunctions[33]! Cache.raw.codes[33]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function33_valid

theorem function34_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 34
      resolvedFunctions[34]! Cache.raw.codes[34]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function34_valid

theorem function35_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 35
      resolvedFunctions[35]! Cache.raw.codes[35]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function35_valid

end Project.TinyGpt2Hidden.Artifact
