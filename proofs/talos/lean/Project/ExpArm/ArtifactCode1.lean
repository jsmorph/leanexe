import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_1_12_e_tail19 :
    instructionSequenceAt 210 false { bytes := artifactBytes, pos := 9171, limit := 9305 } =
      .ok ((((((Cache.raw.codes[1]!).body)[12]!).childBody true).drop 19, .end), { bytes := artifactBytes, pos := 9302, limit := 9305 }) := by
  cbv

@[cbv_eval] theorem sequence_1_12_e_tail0 :
    instructionSequenceAt 229 false { bytes := artifactBytes, pos := 9142, limit := 9305 } =
      .ok ((((((Cache.raw.codes[1]!).body)[12]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 9302, limit := 9305 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail12 :
    instructionSequenceAt 231 false { bytes := artifactBytes, pos := 9097, limit := 9305 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 12, .end), { bytes := artifactBytes, pos := 9305, limit := 9305 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail0 :
    instructionSequenceAt 243 false { bytes := artifactBytes, pos := 9062, limit := 9305 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9305, limit := 9305 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 9057, limit := 10666 } = .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 9305, limit := 10666 }) := by
  refine code_eq_of_parts (size := 246)
    (payload := { bytes := artifactBytes, pos := 9059, limit := 10666 })
    (bodyStart := { bytes := artifactBytes, pos := 9062, limit := 9305 })
    (bodyFinish := { bytes := artifactBytes, pos := 9305, limit := 9305 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_1_tail0
  · rfl

#print axioms code1_decoded

end Project.ExpArm.Artifact
