import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_39_18_t_0_t_tail18 :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 18331, limit := 18621 } =
      .ok ((((((((Cache.raw.codes[39]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 18459, limit := 18621 }) := by
  cbv

@[cbv_eval] theorem sequence_39_18_t_0_t_tail0 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 18300, limit := 18621 } =
      .ok ((((((((Cache.raw.codes[39]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18459, limit := 18621 }) := by
  cbv

@[cbv_eval] theorem sequence_39_18_t_tail0 :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 18298, limit := 18621 } =
      .ok ((((((Cache.raw.codes[39]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18460, limit := 18621 }) := by
  cbv

@[cbv_eval] theorem sequence_39_22_t_tail8 :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 18480, limit := 18621 } =
      .ok ((((((Cache.raw.codes[39]!).body)[22]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 18611, limit := 18621 }) := by
  cbv

@[cbv_eval] theorem sequence_39_22_t_tail0 :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 18467, limit := 18621 } =
      .ok ((((((Cache.raw.codes[39]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18611, limit := 18621 }) := by
  cbv

@[cbv_eval] theorem sequence_39_tail22 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 18465, limit := 18621 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 22, .end), { bytes := artifactBytes, pos := 18621, limit := 18621 }) := by
  cbv

@[cbv_eval] theorem sequence_39_tail18 :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 18296, limit := 18621 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 18, .end), { bytes := artifactBytes, pos := 18621, limit := 18621 }) := by
  cbv

@[cbv_eval] theorem sequence_39_tail0 :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 18259, limit := 18621 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18621, limit := 18621 }) := by
  cbv

theorem code39_decoded :
    code { bytes := artifactBytes, pos := 18254, limit := 19083 } = .ok (Cache.raw.codes[39]!, { bytes := artifactBytes, pos := 18621, limit := 19083 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 18256, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 18259, limit := 18621 })
    (bodyFinish := { bytes := artifactBytes, pos := 18621, limit := 18621 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_39_tail0
  · rfl

#print axioms code39_decoded

end Project.Gpt2CachedStep.Artifact
