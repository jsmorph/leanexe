import Project.Gpt2QuantizedCached.ArtifactCode42Sequences3
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code42_decoded :
    code { bytes := artifactBytes, pos := 11239, limit := 28315 } = .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 13496, limit := 28315 }) := by
  refine code_eq_of_parts (size := 2255)
    (payload := { bytes := artifactBytes, pos := 11241, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 11244, limit := 13496 })
    (bodyFinish := { bytes := artifactBytes, pos := 13496, limit := 13496 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_42_tail0
  · rfl

#print axioms code42_decoded

end Project.Gpt2QuantizedCached.Artifact
