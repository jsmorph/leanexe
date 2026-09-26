import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode34Sequences4

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 7095, limit := 28017 } = .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 9227, limit := 28017 }) := by
  refine code_eq_of_parts (size := 2130)
    (payload := { bytes := artifactBytes, pos := 7097, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 7100, limit := 9227 })
    (bodyFinish := { bytes := artifactBytes, pos := 9227, limit := 9227 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_34_tail0
  · rfl

#print axioms code34_decoded

end Project.Gpt2QuantizedCached.Artifact
