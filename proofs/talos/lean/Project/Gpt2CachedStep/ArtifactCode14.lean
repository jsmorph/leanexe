import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_14_tail0 :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 1197, limit := 1262 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1262, limit := 1262 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 1193, limit := 19083 } = .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 1262, limit := 19083 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 1194, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 1197, limit := 1262 })
    (bodyFinish := { bytes := artifactBytes, pos := 1262, limit := 1262 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_14_tail0
  · rfl

#print axioms code14_decoded

end Project.Gpt2CachedStep.Artifact
