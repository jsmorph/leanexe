import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_26_tail237 :
    instructionSequenceAt 238 false { bytes := artifactBytes, pos := 6619, limit := 6748 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 237, .end), { bytes := artifactBytes, pos := 6748, limit := 6748 }) := by
  cbv

@[cbv_eval] theorem sequence_26_tail148 :
    instructionSequenceAt 327 false { bytes := artifactBytes, pos := 6491, limit := 6748 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 148, .end), { bytes := artifactBytes, pos := 6748, limit := 6748 }) := by
  cbv

@[cbv_eval] theorem sequence_26_tail60 :
    instructionSequenceAt 415 false { bytes := artifactBytes, pos := 6363, limit := 6748 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 60, .end), { bytes := artifactBytes, pos := 6748, limit := 6748 }) := by
  cbv

@[cbv_eval] theorem sequence_26_tail0 :
    instructionSequenceAt 475 false { bytes := artifactBytes, pos := 6273, limit := 6748 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6748, limit := 6748 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 6268, limit := 19083 } = .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 6748, limit := 19083 }) := by
  refine code_eq_of_parts (size := 478)
    (payload := { bytes := artifactBytes, pos := 6270, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 6273, limit := 6748 })
    (bodyFinish := { bytes := artifactBytes, pos := 6748, limit := 6748 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_26_tail0
  · rfl

#print axioms code26_decoded

end Project.Gpt2CachedStep.Artifact
