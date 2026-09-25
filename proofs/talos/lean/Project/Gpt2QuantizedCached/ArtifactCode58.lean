import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode58Sequences3

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code58_decoded :
    code { bytes := artifactBytes, pos := 23674, limit := 28017 } = .ok (Cache.raw.codes[58]!, { bytes := artifactBytes, pos := 25750, limit := 28017 }) := by
  refine code_eq_of_parts (size := 2074)
    (payload := { bytes := artifactBytes, pos := 23676, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 23680, limit := 25750 })
    (bodyFinish := { bytes := artifactBytes, pos := 25750, limit := 25750 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_58_tail0
  · rfl

#print axioms code58_decoded

end Project.Gpt2QuantizedCached.Artifact
