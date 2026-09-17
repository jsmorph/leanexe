import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function8_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 8
      resolvedFunctions[8]! Cache.raw.codes[8]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function8_valid

theorem function9_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 9
      resolvedFunctions[9]! Cache.raw.codes[9]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function9_valid

theorem function10_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 10
      resolvedFunctions[10]! Cache.raw.codes[10]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function10_valid

theorem function11_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 11
      resolvedFunctions[11]! Cache.raw.codes[11]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function11_valid

end Project.TinyGpt2Hidden.Artifact
