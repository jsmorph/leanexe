import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function28_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 28
      resolvedFunctions[28]! Cache.raw.codes[28]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function28_valid

theorem function29_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 29
      resolvedFunctions[29]! Cache.raw.codes[29]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function29_valid

theorem function30_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 30
      resolvedFunctions[30]! Cache.raw.codes[30]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function30_valid

theorem function31_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 31
      resolvedFunctions[31]! Cache.raw.codes[31]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function31_valid

end Project.TinyGpt2Hidden.Artifact
