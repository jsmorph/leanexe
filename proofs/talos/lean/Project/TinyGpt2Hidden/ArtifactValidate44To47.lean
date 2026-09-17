import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function44_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 44
      resolvedFunctions[44]! Cache.raw.codes[44]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function44_valid

theorem function45_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 45
      resolvedFunctions[45]! Cache.raw.codes[45]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function45_valid

theorem function46_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 46
      resolvedFunctions[46]! Cache.raw.codes[46]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function46_valid

theorem function47_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 47
      resolvedFunctions[47]! Cache.raw.codes[47]! = .ok () := by
  apply ok_unit_of_isSome
  decide +kernel

#print axioms function47_valid

end Project.TinyGpt2Hidden.Artifact
