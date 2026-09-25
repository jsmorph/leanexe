import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_25_tail0 :
    instructionSequenceAt 36 false { bytes := artifactBytes, pos := 3282, limit := 3318 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3318, limit := 3318 }) := by
  cbv

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 3278, limit := 28017 } = .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 3318, limit := 28017 }) := by
  refine code_eq_of_parts (size := 39)
    (payload := { bytes := artifactBytes, pos := 3279, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 3282, limit := 3318 })
    (bodyFinish := { bytes := artifactBytes, pos := 3318, limit := 3318 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_25_tail0
  · rfl

#print axioms code25_decoded

end Project.Gpt2QuantizedCached.Artifact
