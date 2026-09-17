import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function24_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 24
      resolvedFunctions[24]! Cache.raw.codes[24]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function24_valid

theorem function25_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 25
      resolvedFunctions[25]! Cache.raw.codes[25]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function25_valid

theorem function26_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 26
      resolvedFunctions[26]! Cache.raw.codes[26]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function26_valid

theorem function27_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 27
      resolvedFunctions[27]! Cache.raw.codes[27]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function27_valid

end Project.TinyGpt2Hidden.Artifact
