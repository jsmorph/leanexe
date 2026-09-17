import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function48_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 48
      resolvedFunctions[48]! Cache.raw.codes[48]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function48_valid

theorem function49_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 49
      resolvedFunctions[49]! Cache.raw.codes[49]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function49_valid

theorem function50_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 50
      resolvedFunctions[50]! Cache.raw.codes[50]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function50_valid

theorem function51_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 51
      resolvedFunctions[51]! Cache.raw.codes[51]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function51_valid

end Project.TinyGpt2Hidden.Artifact
