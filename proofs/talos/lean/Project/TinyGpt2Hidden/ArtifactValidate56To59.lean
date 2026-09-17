import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function56_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 56
      resolvedFunctions[56]! Cache.raw.codes[56]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function56_valid

theorem function57_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 57
      resolvedFunctions[57]! Cache.raw.codes[57]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function57_valid

theorem function58_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 58
      resolvedFunctions[58]! Cache.raw.codes[58]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function58_valid

theorem function59_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 59
      resolvedFunctions[59]! Cache.raw.codes[59]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function59_valid

end Project.TinyGpt2Hidden.Artifact
