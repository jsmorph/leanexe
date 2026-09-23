import Project.Gpt2QuantizedCached.ArtifactCode54Sequences3
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code54_decoded :
    code { bytes := artifactBytes, pos := 20833, limit := 28315 } = .ok (Cache.raw.codes[54]!, { bytes := artifactBytes, pos := 23753, limit := 28315 }) := by
  refine code_eq_of_parts (size := 2918)
    (payload := { bytes := artifactBytes, pos := 20835, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 20839, limit := 23753 })
    (bodyFinish := { bytes := artifactBytes, pos := 23753, limit := 23753 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_54_tail0
  · rfl

#print axioms code54_decoded

end Project.Gpt2QuantizedCached.Artifact
