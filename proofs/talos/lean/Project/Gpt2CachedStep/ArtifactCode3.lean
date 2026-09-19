import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_tail0 :
    instructionSequenceAt 8 false { bytes := artifactBytes, pos := 690, limit := 698 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 698, limit := 698 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 686, limit := 19083 } = .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 698, limit := 19083 }) := by
  refine code_eq_of_parts (size := 11)
    (payload := { bytes := artifactBytes, pos := 687, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 690, limit := 698 })
    (bodyFinish := { bytes := artifactBytes, pos := 698, limit := 698 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_3_tail0
  · rfl

#print axioms code3_decoded

end Project.Gpt2CachedStep.Artifact
