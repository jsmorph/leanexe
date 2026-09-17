import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function60_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 60
      resolvedFunctions[60]! Cache.raw.codes[60]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function60_valid

theorem function61_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 61
      resolvedFunctions[61]! Cache.raw.codes[61]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function61_valid

theorem function62_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 62
      resolvedFunctions[62]! Cache.raw.codes[62]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function62_valid

theorem function63_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 63
      resolvedFunctions[63]! Cache.raw.codes[63]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function63_valid

end Project.TinyGpt2Hidden.Artifact
