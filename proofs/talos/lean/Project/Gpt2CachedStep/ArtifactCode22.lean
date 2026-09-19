import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_22_3_t_tail11 :
    instructionSequenceAt 201 true { bytes := artifactBytes, pos := 5085, limit := 5273 } =
      .ok ((((((Cache.raw.codes[22]!).body)[3]!).childBody false).drop 11, .otherwise), { bytes := artifactBytes, pos := 5213, limit := 5273 }) := by
  cbv

@[cbv_eval] theorem sequence_22_3_t_tail0 :
    instructionSequenceAt 212 true { bytes := artifactBytes, pos := 5063, limit := 5273 } =
      .ok ((((((Cache.raw.codes[22]!).body)[3]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 5213, limit := 5273 }) := by
  cbv

@[cbv_eval] theorem sequence_22_tail3 :
    instructionSequenceAt 214 false { bytes := artifactBytes, pos := 5061, limit := 5273 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 3, .end), { bytes := artifactBytes, pos := 5273, limit := 5273 }) := by
  cbv

@[cbv_eval] theorem sequence_22_tail0 :
    instructionSequenceAt 217 false { bytes := artifactBytes, pos := 5056, limit := 5273 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5273, limit := 5273 }) := by
  cbv

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 5051, limit := 19083 } = .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 5273, limit := 19083 }) := by
  refine code_eq_of_parts (size := 220)
    (payload := { bytes := artifactBytes, pos := 5053, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 5056, limit := 5273 })
    (bodyFinish := { bytes := artifactBytes, pos := 5273, limit := 5273 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_22_tail0
  · rfl

#print axioms code22_decoded

end Project.Gpt2CachedStep.Artifact
