import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function20_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 20
      resolvedFunctions[20]! Cache.raw.codes[20]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function20_valid

theorem function21_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 21
      resolvedFunctions[21]! Cache.raw.codes[21]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function21_valid

theorem function22_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 22
      resolvedFunctions[22]! Cache.raw.codes[22]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function22_valid

theorem function23_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 23
      resolvedFunctions[23]! Cache.raw.codes[23]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function23_valid

end Project.TinyGpt2Hidden.Artifact
