import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_1_tail0 :
    instructionSequenceAt 11 false { bytes := artifactBytes, pos := 800, limit := 811 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 811, limit := 811 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 796, limit := 28017 } = .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 811, limit := 28017 }) := by
  refine code_eq_of_parts (size := 14)
    (payload := { bytes := artifactBytes, pos := 797, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 800, limit := 811 })
    (bodyFinish := { bytes := artifactBytes, pos := 811, limit := 811 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_1_tail0
  · rfl

#print axioms code1_decoded

end Project.Gpt2QuantizedCached.Artifact
