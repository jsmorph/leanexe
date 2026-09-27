import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_36_18_t_0_t_tail18 :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 26316, limit := 26606 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 26444, limit := 26606 }) := by
  cbv

@[cbv_eval] theorem sequence_36_18_t_0_t_tail0 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 26285, limit := 26606 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 26444, limit := 26606 }) := by
  cbv

@[cbv_eval] theorem sequence_36_18_t_tail0 :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 26283, limit := 26606 } =
      .ok ((((((Cache.raw.codes[36]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 26445, limit := 26606 }) := by
  cbv

@[cbv_eval] theorem sequence_36_22_t_tail8 :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 26465, limit := 26606 } =
      .ok ((((((Cache.raw.codes[36]!).body)[22]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 26596, limit := 26606 }) := by
  cbv

@[cbv_eval] theorem sequence_36_22_t_tail0 :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 26452, limit := 26606 } =
      .ok ((((((Cache.raw.codes[36]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 26596, limit := 26606 }) := by
  cbv

@[cbv_eval] theorem sequence_36_tail22 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 26450, limit := 26606 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 22, .end), { bytes := artifactBytes, pos := 26606, limit := 26606 }) := by
  cbv

@[cbv_eval] theorem sequence_36_tail18 :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 26281, limit := 26606 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 18, .end), { bytes := artifactBytes, pos := 26606, limit := 26606 }) := by
  cbv

@[cbv_eval] theorem sequence_36_tail0 :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 26244, limit := 26606 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26606, limit := 26606 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 26239, limit := 27068 } = .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 26606, limit := 27068 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 26241, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 26244, limit := 26606 })
    (bodyFinish := { bytes := artifactBytes, pos := 26606, limit := 26606 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_36_tail0
  · rfl

#print axioms code36_decoded

end Project.Beck.Artifact
