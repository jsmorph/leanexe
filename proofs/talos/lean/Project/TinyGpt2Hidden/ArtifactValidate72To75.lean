import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function72_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 72
      resolvedFunctions[72]! Cache.raw.codes[72]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function72_valid

theorem function73_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 73
      resolvedFunctions[73]! Cache.raw.codes[73]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function73_valid

theorem function74_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 74
      resolvedFunctions[74]! Cache.raw.codes[74]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function74_valid

theorem function75_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 75
      resolvedFunctions[75]! Cache.raw.codes[75]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function75_valid

end Project.TinyGpt2Hidden.Artifact
