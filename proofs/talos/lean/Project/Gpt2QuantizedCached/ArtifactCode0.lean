import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail0 :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 789, limit := 796 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 796, limit := 796 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 785, limit := 28017 } = .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 796, limit := 28017 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 786, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 789, limit := 796 })
    (bodyFinish := { bytes := artifactBytes, pos := 796, limit := 796 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_0_tail0
  · rfl

#print axioms code0_decoded

end Project.Gpt2QuantizedCached.Artifact
