import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_7_18_e_tail95 :
    instructionSequenceAt 304 false { bytes := bytes, pos := 10295, limit := 10437 } =
      .ok ((((((raw.core.codes[7]!).body)[18]!).childBody true).drop 95, .end), { bytes := bytes, pos := 10424, limit := 10437 }) := by
  cbv

@[cbv_eval] theorem sequence_7_18_e_tail43 :
    instructionSequenceAt 356 false { bytes := bytes, pos := 10166, limit := 10437 } =
      .ok ((((((raw.core.codes[7]!).body)[18]!).childBody true).drop 43, .end), { bytes := bytes, pos := 10424, limit := 10437 }) := by
  cbv

@[cbv_eval] theorem sequence_7_18_e_tail0 :
    instructionSequenceAt 399 false { bytes := bytes, pos := 10080, limit := 10437 } =
      .ok ((((((raw.core.codes[7]!).body)[18]!).childBody true).drop 0, .end), { bytes := bytes, pos := 10424, limit := 10437 }) := by
  cbv

@[cbv_eval] theorem sequence_7_tail18 :
    instructionSequenceAt 401 false { bytes := bytes, pos := 10053, limit := 10437 } =
      .ok ((((raw.core.codes[7]!).body).drop 18, .end), { bytes := bytes, pos := 10437, limit := 10437 }) := by
  cbv

@[cbv_eval] theorem sequence_7_tail0 :
    instructionSequenceAt 419 false { bytes := bytes, pos := 10018, limit := 10437 } =
      .ok ((((raw.core.codes[7]!).body).drop 0, .end), { bytes := bytes, pos := 10437, limit := 10437 }) := by
  cbv

theorem code7_decoded :
    code { bytes := bytes, pos := 10013, limit := 16553 } = .ok (raw.core.codes[7]!, { bytes := bytes, pos := 10437, limit := 16553 }) := by
  refine code_eq_of_parts (size := 422)
    (payload := { bytes := bytes, pos := 10015, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 10018, limit := 10437 })
    (bodyFinish := { bytes := bytes, pos := 10437, limit := 10437 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_7_tail0
  · rfl

#print axioms code7_decoded

end Project.RunningSum.Artifact
