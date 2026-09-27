import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.Validate
import Lean.Elab.Tactic.Cbv

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

set_option maxRecDepth 131072 in
set_option cbv.maxSteps 1000000 in
theorem validate_function99 :
    Validator.validateFunction Cache.raw Cache.raw.types 99
      (Cache.raw.types[99]!) (Cache.raw.codes[99]!) = .ok () := by
  cbv

#print axioms validate_function99

end Project.EulerRiemann.Artifact
