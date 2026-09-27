import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_28_12_t_0_t_tail101 :
    instructionSequenceAt 402 false { bytes := artifactBytes, pos := 13836, limit := 14003 } =
      .ok ((((((((Cache.raw.codes[28]!).body)[12]!).childBody false)[0]!).childBody false).drop 101, .end), { bytes := artifactBytes, pos := 13964, limit := 14003 }) := by
  cbv

@[cbv_eval] theorem sequence_28_12_t_0_t_tail58 :
    instructionSequenceAt 445 false { bytes := artifactBytes, pos := 13703, limit := 14003 } =
      .ok ((((((((Cache.raw.codes[28]!).body)[12]!).childBody false)[0]!).childBody false).drop 58, .end), { bytes := artifactBytes, pos := 13964, limit := 14003 }) := by
  cbv

@[cbv_eval] theorem sequence_28_12_t_0_t_tail23 :
    instructionSequenceAt 480 false { bytes := artifactBytes, pos := 13554, limit := 14003 } =
      .ok ((((((((Cache.raw.codes[28]!).body)[12]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := artifactBytes, pos := 13964, limit := 14003 }) := by
  cbv

@[cbv_eval] theorem sequence_28_12_t_0_t_tail0 :
    instructionSequenceAt 503 false { bytes := artifactBytes, pos := 13512, limit := 14003 } =
      .ok ((((((((Cache.raw.codes[28]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13964, limit := 14003 }) := by
  cbv

@[cbv_eval] theorem sequence_28_12_t_tail0 :
    instructionSequenceAt 505 false { bytes := artifactBytes, pos := 13510, limit := 14003 } =
      .ok ((((((Cache.raw.codes[28]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13965, limit := 14003 }) := by
  cbv

@[cbv_eval] theorem sequence_28_tail12 :
    instructionSequenceAt 507 false { bytes := artifactBytes, pos := 13508, limit := 14003 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 12, .end), { bytes := artifactBytes, pos := 14003, limit := 14003 }) := by
  cbv

@[cbv_eval] theorem sequence_28_tail0 :
    instructionSequenceAt 519 false { bytes := artifactBytes, pos := 13484, limit := 14003 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14003, limit := 14003 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 13479, limit := 27068 } = .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 14003, limit := 27068 }) := by
  refine code_eq_of_parts (size := 522)
    (payload := { bytes := artifactBytes, pos := 13481, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 13484, limit := 14003 })
    (bodyFinish := { bytes := artifactBytes, pos := 14003, limit := 14003 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_28_tail0
  · rfl

#print axioms code28_decoded

end Project.Beck.Artifact
