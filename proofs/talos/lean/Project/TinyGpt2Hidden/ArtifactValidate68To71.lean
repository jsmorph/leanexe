import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function68_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 68
      resolvedFunctions[68]! Cache.raw.codes[68]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function68_valid

theorem function69_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 69
      resolvedFunctions[69]! Cache.raw.codes[69]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function69_valid

theorem function70_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 70
      resolvedFunctions[70]! Cache.raw.codes[70]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function70_valid

theorem function71_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 71
      resolvedFunctions[71]! Cache.raw.codes[71]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function71_valid

end Project.TinyGpt2Hidden.Artifact
