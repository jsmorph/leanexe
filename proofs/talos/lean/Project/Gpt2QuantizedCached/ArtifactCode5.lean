import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_5_tail0 :
    instructionSequenceAt 43 false { bytes := artifactBytes, pos := 1064, limit := 1107 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1107, limit := 1107 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 1060, limit := 28017 } = .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 1107, limit := 28017 }) := by
  refine code_eq_of_parts (size := 46)
    (payload := { bytes := artifactBytes, pos := 1061, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 1064, limit := 1107 })
    (bodyFinish := { bytes := artifactBytes, pos := 1107, limit := 1107 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_5_tail0
  · rfl

#print axioms code5_decoded

end Project.Gpt2QuantizedCached.Artifact
