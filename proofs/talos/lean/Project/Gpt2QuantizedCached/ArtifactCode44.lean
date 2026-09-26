import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_44_10_t_0_t_tail67 :
    instructionSequenceAt 281 false { bytes := artifactBytes, pos := 13840, limit := 13997 } =
      .ok ((((((((Cache.raw.codes[44]!).body)[10]!).childBody false)[0]!).childBody false).drop 67, .end), { bytes := artifactBytes, pos := 13968, limit := 13997 }) := by
  cbv

@[cbv_eval] theorem sequence_44_10_t_0_t_tail21 :
    instructionSequenceAt 327 false { bytes := artifactBytes, pos := 13701, limit := 13997 } =
      .ok ((((((((Cache.raw.codes[44]!).body)[10]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 13968, limit := 13997 }) := by
  cbv

@[cbv_eval] theorem sequence_44_10_t_0_t_tail0 :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 13660, limit := 13997 } =
      .ok ((((((((Cache.raw.codes[44]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13968, limit := 13997 }) := by
  cbv

@[cbv_eval] theorem sequence_44_10_t_tail0 :
    instructionSequenceAt 350 false { bytes := artifactBytes, pos := 13658, limit := 13997 } =
      .ok ((((((Cache.raw.codes[44]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13969, limit := 13997 }) := by
  cbv

@[cbv_eval] theorem sequence_44_tail10 :
    instructionSequenceAt 352 false { bytes := artifactBytes, pos := 13656, limit := 13997 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 10, .end), { bytes := artifactBytes, pos := 13997, limit := 13997 }) := by
  cbv

@[cbv_eval] theorem sequence_44_tail0 :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 13635, limit := 13997 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13997, limit := 13997 }) := by
  cbv

theorem code44_decoded :
    code { bytes := artifactBytes, pos := 13630, limit := 28017 } = .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 13997, limit := 28017 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 13632, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 13635, limit := 13997 })
    (bodyFinish := { bytes := artifactBytes, pos := 13997, limit := 13997 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_44_tail0
  · rfl

#print axioms code44_decoded

end Project.Gpt2QuantizedCached.Artifact
