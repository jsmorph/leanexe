import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_12_tail0 :
    instructionSequenceAt 67 false { bytes := artifactBytes, pos := 1091, limit := 1158 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1158, limit := 1158 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 1087, limit := 19083 } = .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 1158, limit := 19083 }) := by
  refine code_eq_of_parts (size := 70)
    (payload := { bytes := artifactBytes, pos := 1088, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 1091, limit := 1158 })
    (bodyFinish := { bytes := artifactBytes, pos := 1158, limit := 1158 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_12_tail0
  · rfl

#print axioms code12_decoded

end Project.Gpt2CachedStep.Artifact
