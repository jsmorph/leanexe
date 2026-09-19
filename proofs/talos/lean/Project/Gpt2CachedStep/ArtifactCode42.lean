import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_42_tail43 :
    instructionSequenceAt 305 false { bytes := artifactBytes, pos := 18923, limit := 19083 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 43, .end), { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  cbv

@[cbv_eval] theorem sequence_42_tail25 :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 18794, limit := 19083 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 25, .end), { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  cbv

@[cbv_eval] theorem sequence_42_tail0 :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 18735, limit := 19083 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  cbv

theorem code42_decoded :
    code { bytes := artifactBytes, pos := 18730, limit := 19083 } = .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 18732, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 18735, limit := 19083 })
    (bodyFinish := { bytes := artifactBytes, pos := 19083, limit := 19083 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_42_tail0
  · rfl

#print axioms code42_decoded

end Project.Gpt2CachedStep.Artifact
