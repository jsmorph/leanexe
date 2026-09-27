import Project.EulerOutwardFaceStep.ArtifactCache
import Project.EulerOutwardFaceStep.ArtifactValidationExports
import Project.Artifact.Binary.ValidationParts
import Lean.Elab.Tactic.Cbv

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem validation_sections : Validator.validateSections Cache.raw = .ok () := by cbv
theorem validation_memory : Cache.raw.memories.length = 1 := by rfl
theorem validation_limits :
    Validator.validateLimits Cache.raw.memories.head!.limits = .ok () := by cbv
theorem validation_globals : Validator.validateGlobals Cache.raw.globals = .ok () := by cbv
theorem validation_types : Validator.resolveFunctionTypes Cache.raw = .ok Cache.raw.types := by cbv

#print axioms validation_sections
#print axioms validation_limits
#print axioms validation_globals
#print axioms validation_exports
#print axioms validation_types
end Project.EulerOutwardFaceStep.Artifact
