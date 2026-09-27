import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_18_t_0_t_tail18 :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 9914, limit := 10204 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 10042, limit := 10204 }) := by
  cbv

@[cbv_eval] theorem sequence_3_18_t_0_t_tail0 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 9883, limit := 10204 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10042, limit := 10204 }) := by
  cbv

@[cbv_eval] theorem sequence_3_18_t_tail0 :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 9881, limit := 10204 } =
      .ok ((((((Cache.raw.codes[3]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10043, limit := 10204 }) := by
  cbv

@[cbv_eval] theorem sequence_3_22_t_tail8 :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 10063, limit := 10204 } =
      .ok ((((((Cache.raw.codes[3]!).body)[22]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 10194, limit := 10204 }) := by
  cbv

@[cbv_eval] theorem sequence_3_22_t_tail0 :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 10050, limit := 10204 } =
      .ok ((((((Cache.raw.codes[3]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10194, limit := 10204 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail22 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 10048, limit := 10204 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 22, .end), { bytes := artifactBytes, pos := 10204, limit := 10204 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail18 :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 9879, limit := 10204 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 18, .end), { bytes := artifactBytes, pos := 10204, limit := 10204 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail0 :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 9842, limit := 10204 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10204, limit := 10204 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 9837, limit := 10666 } = .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 10204, limit := 10666 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 9839, limit := 10666 })
    (bodyStart := { bytes := artifactBytes, pos := 9842, limit := 10204 })
    (bodyFinish := { bytes := artifactBytes, pos := 10204, limit := 10204 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_3_tail0
  · rfl

#print axioms code3_decoded

end Project.ExpArm.Artifact
