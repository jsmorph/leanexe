import Project.Gpt2QuantizedCached.ArtifactCode51Sequences1
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code51_decoded :
    code { bytes := artifactBytes, pos := 19510, limit := 28315 } = .ok (Cache.raw.codes[51]!, { bytes := artifactBytes, pos := 20067, limit := 28315 }) := by
  refine code_eq_of_parts (size := 555)
    (payload := { bytes := artifactBytes, pos := 19512, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 19515, limit := 20067 })
    (bodyFinish := { bytes := artifactBytes, pos := 20067, limit := 20067 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_51_tail0
  · rfl

#print axioms code51_decoded

end Project.Gpt2QuantizedCached.Artifact
