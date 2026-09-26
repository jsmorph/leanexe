import Project.Gpt2QuantizedGroupedRows.ArtifactValidationExports
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.ValidationParts
import Lean.Elab.Tactic.Cbv

namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

def resolvedTypes : List FuncType :=
  Cache.raw.functionTypeIndices.map (fun index => Cache.raw.types[index.toNat]!)

theorem validation_sections : Validator.validateSections Cache.raw = .ok () := by cbv
theorem validation_memory : Cache.raw.memories.length = 1 := by rfl
theorem validation_limits : Validator.validateLimits Cache.raw.memories.head!.limits = .ok () := by cbv
theorem validation_globals : Validator.validateGlobals Cache.raw.globals = .ok () := by cbv
theorem validation_types : Validator.resolveFunctionTypes Cache.raw = .ok resolvedTypes := by cbv

end Project.Gpt2QuantizedGroupedRows.Artifact
