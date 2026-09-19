import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_23_12_t_0_t_tail69 :
    instructionSequenceAt 285 false { bytes := artifactBytes, pos := 5491, limit := 5648 } =
      .ok ((((((((Cache.raw.codes[23]!).body)[12]!).childBody false)[0]!).childBody false).drop 69, .end), { bytes := artifactBytes, pos := 5619, limit := 5648 }) := by
  cbv

@[cbv_eval] theorem sequence_23_12_t_0_t_tail21 :
    instructionSequenceAt 333 false { bytes := artifactBytes, pos := 5348, limit := 5648 } =
      .ok ((((((((Cache.raw.codes[23]!).body)[12]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 5619, limit := 5648 }) := by
  cbv

@[cbv_eval] theorem sequence_23_12_t_0_t_tail0 :
    instructionSequenceAt 354 false { bytes := artifactBytes, pos := 5307, limit := 5648 } =
      .ok ((((((((Cache.raw.codes[23]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5619, limit := 5648 }) := by
  cbv

@[cbv_eval] theorem sequence_23_12_t_tail0 :
    instructionSequenceAt 356 false { bytes := artifactBytes, pos := 5305, limit := 5648 } =
      .ok ((((((Cache.raw.codes[23]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5620, limit := 5648 }) := by
  cbv

@[cbv_eval] theorem sequence_23_tail12 :
    instructionSequenceAt 358 false { bytes := artifactBytes, pos := 5303, limit := 5648 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 12, .end), { bytes := artifactBytes, pos := 5648, limit := 5648 }) := by
  cbv

@[cbv_eval] theorem sequence_23_tail0 :
    instructionSequenceAt 370 false { bytes := artifactBytes, pos := 5278, limit := 5648 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5648, limit := 5648 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 5273, limit := 19083 } = .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 5648, limit := 19083 }) := by
  refine code_eq_of_parts (size := 373)
    (payload := { bytes := artifactBytes, pos := 5275, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 5278, limit := 5648 })
    (bodyFinish := { bytes := artifactBytes, pos := 5648, limit := 5648 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_23_tail0
  · rfl

#print axioms code23_decoded

end Project.Gpt2CachedStep.Artifact
