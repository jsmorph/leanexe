import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_28_12_t_0_t_tail21 :
    instructionSequenceAt 174 false { bytes := artifactBytes, pos := 7202, limit := 7346 } =
      .ok ((((((((Cache.raw.codes[28]!).body)[12]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 7330, limit := 7346 }) := by
  cbv

@[cbv_eval] theorem sequence_28_12_t_0_t_tail0 :
    instructionSequenceAt 195 false { bytes := artifactBytes, pos := 7163, limit := 7346 } =
      .ok ((((((((Cache.raw.codes[28]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7330, limit := 7346 }) := by
  cbv

@[cbv_eval] theorem sequence_28_12_t_tail0 :
    instructionSequenceAt 197 false { bytes := artifactBytes, pos := 7161, limit := 7346 } =
      .ok ((((((Cache.raw.codes[28]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7331, limit := 7346 }) := by
  cbv

@[cbv_eval] theorem sequence_28_tail12 :
    instructionSequenceAt 199 false { bytes := artifactBytes, pos := 7159, limit := 7346 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 12, .end), { bytes := artifactBytes, pos := 7346, limit := 7346 }) := by
  cbv

@[cbv_eval] theorem sequence_28_tail0 :
    instructionSequenceAt 211 false { bytes := artifactBytes, pos := 7135, limit := 7346 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7346, limit := 7346 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 7130, limit := 19083 } = .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 7346, limit := 19083 }) := by
  refine code_eq_of_parts (size := 214)
    (payload := { bytes := artifactBytes, pos := 7132, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 7135, limit := 7346 })
    (bodyFinish := { bytes := artifactBytes, pos := 7346, limit := 7346 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_28_tail0
  · rfl

#print axioms code28_decoded

end Project.Gpt2CachedStep.Artifact
