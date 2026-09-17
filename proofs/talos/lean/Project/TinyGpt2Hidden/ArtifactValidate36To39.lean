import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function36_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 36
      resolvedFunctions[36]! Cache.raw.codes[36]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function36_valid

theorem function37_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 37
      resolvedFunctions[37]! Cache.raw.codes[37]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function37_valid

theorem function38_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 38
      resolvedFunctions[38]! Cache.raw.codes[38]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function38_valid

theorem function39_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 39
      resolvedFunctions[39]! Cache.raw.codes[39]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function39_valid

end Project.TinyGpt2Hidden.Artifact
