import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_19_12_t_0_t_tail21 :
    instructionSequenceAt 250 false { bytes := artifactBytes, pos := 1739, limit := 1956 } =
      .ok ((((((((Cache.raw.codes[19]!).body)[12]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 1888, limit := 1956 }) := by
  cbv

@[cbv_eval] theorem sequence_19_12_t_0_t_tail0 :
    instructionSequenceAt 271 false { bytes := artifactBytes, pos := 1698, limit := 1956 } =
      .ok ((((((((Cache.raw.codes[19]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1888, limit := 1956 }) := by
  cbv

@[cbv_eval] theorem sequence_19_12_t_tail0 :
    instructionSequenceAt 273 false { bytes := artifactBytes, pos := 1696, limit := 1956 } =
      .ok ((((((Cache.raw.codes[19]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1889, limit := 1956 }) := by
  cbv

@[cbv_eval] theorem sequence_19_tail12 :
    instructionSequenceAt 275 false { bytes := artifactBytes, pos := 1694, limit := 1956 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 12, .end), { bytes := artifactBytes, pos := 1956, limit := 1956 }) := by
  cbv

@[cbv_eval] theorem sequence_19_tail0 :
    instructionSequenceAt 287 false { bytes := artifactBytes, pos := 1669, limit := 1956 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1956, limit := 1956 }) := by
  cbv

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 1664, limit := 19083 } = .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 1956, limit := 19083 }) := by
  refine code_eq_of_parts (size := 290)
    (payload := { bytes := artifactBytes, pos := 1666, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 1669, limit := 1956 })
    (bodyFinish := { bytes := artifactBytes, pos := 1956, limit := 1956 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_19_tail0
  · rfl

#print axioms code19_decoded

end Project.Gpt2CachedStep.Artifact
