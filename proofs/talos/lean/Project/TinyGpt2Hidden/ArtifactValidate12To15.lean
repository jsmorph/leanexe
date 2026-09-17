import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function12_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 12
      resolvedFunctions[12]! Cache.raw.codes[12]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function12_valid

theorem function13_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 13
      resolvedFunctions[13]! Cache.raw.codes[13]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function13_valid

theorem function14_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 14
      resolvedFunctions[14]! Cache.raw.codes[14]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function14_valid

theorem function15_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 15
      resolvedFunctions[15]! Cache.raw.codes[15]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function15_valid

end Project.TinyGpt2Hidden.Artifact
