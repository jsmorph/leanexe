import Project.TinyGpt2Hidden.ArtifactValidationTypes

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

theorem function0_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 0
      resolvedFunctions[0]! Cache.raw.codes[0]! = .ok () := by cbv

#print axioms function0_valid

theorem function1_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 1
      resolvedFunctions[1]! Cache.raw.codes[1]! = .ok () := by cbv

#print axioms function1_valid

theorem function2_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 2
      resolvedFunctions[2]! Cache.raw.codes[2]! = .ok () := by cbv

#print axioms function2_valid

theorem function3_valid :
    Validator.validateFunction Cache.raw resolvedFunctions 3
      resolvedFunctions[3]! Cache.raw.codes[3]! = .ok () := by cbv

#print axioms function3_valid

end Project.TinyGpt2Hidden.Artifact
