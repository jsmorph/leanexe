import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function4_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 4
      resolvedFunctions[4]! Cache.raw.codes[4]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function4_valid

theorem function5_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 5
      resolvedFunctions[5]! Cache.raw.codes[5]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function5_valid

theorem function6_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 6
      resolvedFunctions[6]! Cache.raw.codes[6]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function6_valid

theorem function7_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 7
      resolvedFunctions[7]! Cache.raw.codes[7]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function7_valid

end Project.TinyGpt2Hidden.Artifact
