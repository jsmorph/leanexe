import LeanExeGen.GeneratedR1b9b2027715ddee5.ArtifactDecode
import Project.Artifact.Binary.Evidence

namespace LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact

open Wasm.Binary

def cacheValidationSucceeded : Bool :=
  (validate Cache.raw).toOption.isSome

theorem cache_validation_test : cacheValidationSucceeded = true := by
  native_decide

theorem cache_validation_exists :
    ∃ validated, validate Cache.raw = .ok validated := by
  exact ok_exists_of_toOption_isSome cache_validation_test

end LeanExeGen.GeneratedR1b9b2027715ddee5.Artifact
