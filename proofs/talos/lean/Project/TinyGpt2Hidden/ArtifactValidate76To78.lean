import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function76_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 76
      resolvedFunctions[76]! Cache.raw.codes[76]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function76_valid

theorem function77_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 77
      resolvedFunctions[77]! Cache.raw.codes[77]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function77_valid

theorem function78_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 78
      resolvedFunctions[78]! Cache.raw.codes[78]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function78_valid

end Project.TinyGpt2Hidden.Artifact
