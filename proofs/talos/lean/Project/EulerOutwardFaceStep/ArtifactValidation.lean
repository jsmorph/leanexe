import Project.EulerOutwardFaceStep.ArtifactDecode
import Project.EulerOutwardFaceStep.ArtifactValidationMetadata
import Project.Artifact.Binary.Evidence
import Lean.Elab.Tactic.Cbv

namespace Project.EulerOutwardFaceStep.Artifact

open Wasm.Binary

def cacheValidationSucceeded : Bool :=
  (validate Cache.raw).toOption.isSome

set_option maxRecDepth 131072 in
set_option cbv.maxSteps 1000000 in
theorem validation_functions : Validator.validateFunctions Cache.raw Cache.raw.types = .ok () := by
  cbv

theorem cache_validation_test : cacheValidationSucceeded = true := by
  have hraw := validateRaw_eq_of_parts validation_sections validation_memory
    validation_limits validation_globals validation_exports validation_types validation_functions
  unfold cacheValidationSucceeded validate
  rw [hraw]
  rfl

theorem cache_validation_exists :
    ∃ validated, validate Cache.raw = .ok validated := by
  exact ok_exists_of_toOption_isSome cache_validation_test

#print axioms validation_functions
#print axioms cache_validation_test
#print axioms cache_validation_exists
end Project.EulerOutwardFaceStep.Artifact
