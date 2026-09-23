import Project.Gpt2QuantizedCached.ArtifactCode58Sequences3
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code58_decoded :
    code { bytes := artifactBytes, pos := 23810, limit := 28315 } = .ok (Cache.raw.codes[58]!, { bytes := artifactBytes, pos := 26048, limit := 28315 }) := by
  refine code_eq_of_parts (size := 2236)
    (payload := { bytes := artifactBytes, pos := 23812, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 23816, limit := 26048 })
    (bodyFinish := { bytes := artifactBytes, pos := 26048, limit := 26048 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_58_tail0
  · rfl

#print axioms code58_decoded

end Project.Gpt2QuantizedCached.Artifact
