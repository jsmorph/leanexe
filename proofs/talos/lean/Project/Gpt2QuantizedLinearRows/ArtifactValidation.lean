import Project.Gpt2QuantizedLinearRows.ArtifactValidationMetadata
import Project.Gpt2QuantizedLinearRows.ArtifactDecode
import Project.Artifact.Binary.Evidence
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.ValidationParts
import Lean.Elab.Tactic.Cbv

namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem validation_functions : Validator.validateFunctions Cache.raw resolvedTypes = .ok () := by cbv

def cacheValidationSucceeded : Bool := (validate Cache.raw).toOption.isSome

theorem cache_validation_test : cacheValidationSucceeded = true := by
  have hraw := validateRaw_eq_of_parts validation_sections validation_memory
    validation_limits validation_globals validation_exports validation_types validation_functions
  unfold cacheValidationSucceeded validate
  rw [hraw]
  rfl

theorem cache_validation_exists : ∃ validated, validate Cache.raw = .ok validated :=
  ok_exists_of_toOption_isSome cache_validation_test

#print axioms validation_functions
#print axioms cache_validation_exists

end Project.Gpt2QuantizedLinearRows.Artifact
