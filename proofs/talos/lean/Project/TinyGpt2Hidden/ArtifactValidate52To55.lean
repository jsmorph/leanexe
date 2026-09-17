import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function52_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 52
      resolvedFunctions[52]! Cache.raw.codes[52]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function52_valid

theorem function53_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 53
      resolvedFunctions[53]! Cache.raw.codes[53]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function53_valid

theorem function54_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 54
      resolvedFunctions[54]! Cache.raw.codes[54]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function54_valid

theorem function55_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 55
      resolvedFunctions[55]! Cache.raw.codes[55]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function55_valid

end Project.TinyGpt2Hidden.Artifact
