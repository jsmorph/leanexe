import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_60_tail0 :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 27121, limit := 27134 } =
      .ok ((((Cache.raw.codes[60]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27134, limit := 27134 }) := by
  cbv

theorem code60_decoded :
    code { bytes := artifactBytes, pos := 27117, limit := 28017 } = .ok (Cache.raw.codes[60]!, { bytes := artifactBytes, pos := 27134, limit := 28017 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 27118, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 27121, limit := 27134 })
    (bodyFinish := { bytes := artifactBytes, pos := 27134, limit := 27134 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_60_tail0
  · rfl

#print axioms code60_decoded

end Project.Gpt2QuantizedCached.Artifact
