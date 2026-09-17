import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function64_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 64
      resolvedFunctions[64]! Cache.raw.codes[64]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function64_valid

theorem function65_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 65
      resolvedFunctions[65]! Cache.raw.codes[65]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function65_valid

theorem function66_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 66
      resolvedFunctions[66]! Cache.raw.codes[66]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function66_valid

theorem function67_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 67
      resolvedFunctions[67]! Cache.raw.codes[67]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function67_valid

end Project.TinyGpt2Hidden.Artifact
