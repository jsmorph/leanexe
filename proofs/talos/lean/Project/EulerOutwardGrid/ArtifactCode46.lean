import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_46_18_t_0_t_tail18 :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 4968, limit := 5258 } =
      .ok ((((((((Cache.raw.codes[46]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 5096, limit := 5258 }) := by
  cbv

@[cbv_eval] theorem sequence_46_18_t_0_t_tail0 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 4937, limit := 5258 } =
      .ok ((((((((Cache.raw.codes[46]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5096, limit := 5258 }) := by
  cbv

@[cbv_eval] theorem sequence_46_18_t_tail0 :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 4935, limit := 5258 } =
      .ok ((((((Cache.raw.codes[46]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5097, limit := 5258 }) := by
  cbv

@[cbv_eval] theorem sequence_46_22_t_tail8 :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 5117, limit := 5258 } =
      .ok ((((((Cache.raw.codes[46]!).body)[22]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 5248, limit := 5258 }) := by
  cbv

@[cbv_eval] theorem sequence_46_22_t_tail0 :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 5104, limit := 5258 } =
      .ok ((((((Cache.raw.codes[46]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5248, limit := 5258 }) := by
  cbv

@[cbv_eval] theorem sequence_46_tail22 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 5102, limit := 5258 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 22, .end), { bytes := artifactBytes, pos := 5258, limit := 5258 }) := by
  cbv

@[cbv_eval] theorem sequence_46_tail18 :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 4933, limit := 5258 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 18, .end), { bytes := artifactBytes, pos := 5258, limit := 5258 }) := by
  cbv

@[cbv_eval] theorem sequence_46_tail0 :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 4896, limit := 5258 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5258, limit := 5258 }) := by
  cbv

theorem code46_decoded :
    code { bytes := artifactBytes, pos := 4891, limit := 5720 } = .ok (Cache.raw.codes[46]!, { bytes := artifactBytes, pos := 5258, limit := 5720 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 4893, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 4896, limit := 5258 })
    (bodyFinish := { bytes := artifactBytes, pos := 5258, limit := 5258 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_46_tail0
  · rfl

#print axioms code46_decoded

end Project.EulerOutwardGrid.Artifact
