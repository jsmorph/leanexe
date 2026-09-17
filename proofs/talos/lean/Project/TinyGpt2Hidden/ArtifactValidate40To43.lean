import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function40_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 40
      resolvedFunctions[40]! Cache.raw.codes[40]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function40_valid

theorem function41_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 41
      resolvedFunctions[41]! Cache.raw.codes[41]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function41_valid

theorem function42_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 42
      resolvedFunctions[42]! Cache.raw.codes[42]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function42_valid

theorem function43_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 43
      resolvedFunctions[43]! Cache.raw.codes[43]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function43_valid

end Project.TinyGpt2Hidden.Artifact
