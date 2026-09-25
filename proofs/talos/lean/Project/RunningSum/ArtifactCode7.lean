import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_7_18_e_tail103 :
    instructionSequenceAt 320 false { bytes := bytes, pos := 10801, limit := 10942 } =
      .ok ((((((raw.core.codes[7]!).body)[18]!).childBody true).drop 103, .end), { bytes := bytes, pos := 10929, limit := 10942 }) := by
  cbv

@[cbv_eval] theorem sequence_7_18_e_tail56 :
    instructionSequenceAt 367 false { bytes := bytes, pos := 10673, limit := 10942 } =
      .ok ((((((raw.core.codes[7]!).body)[18]!).childBody true).drop 56, .end), { bytes := bytes, pos := 10929, limit := 10942 }) := by
  cbv

@[cbv_eval] theorem sequence_7_18_e_tail0 :
    instructionSequenceAt 423 false { bytes := bytes, pos := 10561, limit := 10942 } =
      .ok ((((((raw.core.codes[7]!).body)[18]!).childBody true).drop 0, .end), { bytes := bytes, pos := 10929, limit := 10942 }) := by
  cbv

@[cbv_eval] theorem sequence_7_tail18 :
    instructionSequenceAt 425 false { bytes := bytes, pos := 10534, limit := 10942 } =
      .ok ((((raw.core.codes[7]!).body).drop 18, .end), { bytes := bytes, pos := 10942, limit := 10942 }) := by
  cbv

@[cbv_eval] theorem sequence_7_tail0 :
    instructionSequenceAt 443 false { bytes := bytes, pos := 10499, limit := 10942 } =
      .ok ((((raw.core.codes[7]!).body).drop 0, .end), { bytes := bytes, pos := 10942, limit := 10942 }) := by
  cbv

theorem code7_decoded :
    code { bytes := bytes, pos := 10494, limit := 16469 } = .ok (raw.core.codes[7]!, { bytes := bytes, pos := 10942, limit := 16469 }) := by
  refine code_eq_of_parts (size := 446)
    (payload := { bytes := bytes, pos := 10496, limit := 16469 })
    (bodyStart := { bytes := bytes, pos := 10499, limit := 10942 })
    (bodyFinish := { bytes := bytes, pos := 10942, limit := 10942 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_7_tail0
  · rfl

#print axioms code7_decoded

end Project.RunningSum.Artifact
