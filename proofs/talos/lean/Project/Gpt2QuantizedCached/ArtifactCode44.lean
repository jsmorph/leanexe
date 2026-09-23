import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_44_12_t_0_t_tail69 :
    instructionSequenceAt 285 false { bytes := artifactBytes, pos := 13936, limit := 14093 } =
      .ok ((((((((Cache.raw.codes[44]!).body)[12]!).childBody false)[0]!).childBody false).drop 69, .end), { bytes := artifactBytes, pos := 14064, limit := 14093 }) := by
  cbv

@[cbv_eval] theorem sequence_44_12_t_0_t_tail21 :
    instructionSequenceAt 333 false { bytes := artifactBytes, pos := 13793, limit := 14093 } =
      .ok ((((((((Cache.raw.codes[44]!).body)[12]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 14064, limit := 14093 }) := by
  cbv

@[cbv_eval] theorem sequence_44_12_t_0_t_tail0 :
    instructionSequenceAt 354 false { bytes := artifactBytes, pos := 13752, limit := 14093 } =
      .ok ((((((((Cache.raw.codes[44]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14064, limit := 14093 }) := by
  cbv

@[cbv_eval] theorem sequence_44_12_t_tail0 :
    instructionSequenceAt 356 false { bytes := artifactBytes, pos := 13750, limit := 14093 } =
      .ok ((((((Cache.raw.codes[44]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14065, limit := 14093 }) := by
  cbv

@[cbv_eval] theorem sequence_44_tail12 :
    instructionSequenceAt 358 false { bytes := artifactBytes, pos := 13748, limit := 14093 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 12, .end), { bytes := artifactBytes, pos := 14093, limit := 14093 }) := by
  cbv

@[cbv_eval] theorem sequence_44_tail0 :
    instructionSequenceAt 370 false { bytes := artifactBytes, pos := 13723, limit := 14093 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14093, limit := 14093 }) := by
  cbv

theorem code44_decoded :
    code { bytes := artifactBytes, pos := 13718, limit := 28315 } = .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 14093, limit := 28315 }) := by
  refine code_eq_of_parts (size := 373)
    (payload := { bytes := artifactBytes, pos := 13720, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 13723, limit := 14093 })
    (bodyFinish := { bytes := artifactBytes, pos := 14093, limit := 14093 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_44_tail0
  · rfl

#print axioms code44_decoded

end Project.Gpt2QuantizedCached.Artifact
