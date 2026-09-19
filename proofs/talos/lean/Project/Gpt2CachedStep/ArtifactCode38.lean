import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_38_25_e_tail102 :
    instructionSequenceAt 449 false { bytes := artifactBytes, pos := 18116, limit := 18254 } =
      .ok ((((((Cache.raw.codes[38]!).body)[25]!).childBody true).drop 102, .end), { bytes := artifactBytes, pos := 18245, limit := 18254 }) := by
  cbv

@[cbv_eval] theorem sequence_38_25_e_tail40 :
    instructionSequenceAt 511 false { bytes := artifactBytes, pos := 17988, limit := 18254 } =
      .ok ((((((Cache.raw.codes[38]!).body)[25]!).childBody true).drop 40, .end), { bytes := artifactBytes, pos := 18245, limit := 18254 }) := by
  cbv

@[cbv_eval] theorem sequence_38_25_e_tail0 :
    instructionSequenceAt 551 false { bytes := artifactBytes, pos := 17905, limit := 18254 } =
      .ok ((((((Cache.raw.codes[38]!).body)[25]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 18245, limit := 18254 }) := by
  cbv

@[cbv_eval] theorem sequence_38_tail25 :
    instructionSequenceAt 553 false { bytes := artifactBytes, pos := 17878, limit := 18254 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 25, .end), { bytes := artifactBytes, pos := 18254, limit := 18254 }) := by
  cbv

@[cbv_eval] theorem sequence_38_tail16 :
    instructionSequenceAt 562 false { bytes := artifactBytes, pos := 17749, limit := 18254 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 16, .end), { bytes := artifactBytes, pos := 18254, limit := 18254 }) := by
  cbv

@[cbv_eval] theorem sequence_38_tail0 :
    instructionSequenceAt 578 false { bytes := artifactBytes, pos := 17676, limit := 18254 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18254, limit := 18254 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 17671, limit := 19083 } = .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 18254, limit := 19083 }) := by
  refine code_eq_of_parts (size := 581)
    (payload := { bytes := artifactBytes, pos := 17673, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 17676, limit := 18254 })
    (bodyFinish := { bytes := artifactBytes, pos := 18254, limit := 18254 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_38_tail0
  · rfl

#print axioms code38_decoded

end Project.Gpt2CachedStep.Artifact
