import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_7_e_3_e_tail108 :
    instructionSequenceAt 405 false { bytes := artifactBytes, pos := 9704, limit := 9837 } =
      .ok ((((((((Cache.raw.codes[2]!).body)[7]!).childBody true)[3]!).childBody true).drop 108, .end), { bytes := artifactBytes, pos := 9833, limit := 9837 }) := by
  cbv

@[cbv_eval] theorem sequence_2_7_e_3_e_tail58 :
    instructionSequenceAt 455 false { bytes := artifactBytes, pos := 9561, limit := 9837 } =
      .ok ((((((((Cache.raw.codes[2]!).body)[7]!).childBody true)[3]!).childBody true).drop 58, .end), { bytes := artifactBytes, pos := 9833, limit := 9837 }) := by
  cbv

@[cbv_eval] theorem sequence_2_7_e_3_e_tail0 :
    instructionSequenceAt 513 false { bytes := artifactBytes, pos := 9429, limit := 9837 } =
      .ok ((((((((Cache.raw.codes[2]!).body)[7]!).childBody true)[3]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 9833, limit := 9837 }) := by
  cbv

@[cbv_eval] theorem sequence_2_7_e_tail3 :
    instructionSequenceAt 515 false { bytes := artifactBytes, pos := 9368, limit := 9837 } =
      .ok ((((((Cache.raw.codes[2]!).body)[7]!).childBody true).drop 3, .end), { bytes := artifactBytes, pos := 9834, limit := 9837 }) := by
  cbv

@[cbv_eval] theorem sequence_2_7_e_tail0 :
    instructionSequenceAt 518 false { bytes := artifactBytes, pos := 9354, limit := 9837 } =
      .ok ((((((Cache.raw.codes[2]!).body)[7]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 9834, limit := 9837 }) := by
  cbv

@[cbv_eval] theorem sequence_2_tail7 :
    instructionSequenceAt 520 false { bytes := artifactBytes, pos := 9339, limit := 9837 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 7, .end), { bytes := artifactBytes, pos := 9837, limit := 9837 }) := by
  cbv

@[cbv_eval] theorem sequence_2_tail0 :
    instructionSequenceAt 527 false { bytes := artifactBytes, pos := 9310, limit := 9837 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9837, limit := 9837 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 9305, limit := 10666 } = .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 9837, limit := 10666 }) := by
  refine code_eq_of_parts (size := 530)
    (payload := { bytes := artifactBytes, pos := 9307, limit := 10666 })
    (bodyStart := { bytes := artifactBytes, pos := 9310, limit := 9837 })
    (bodyFinish := { bytes := artifactBytes, pos := 9837, limit := 9837 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_2_tail0
  · rfl

#print axioms code2_decoded

end Project.ExpArm.Artifact
