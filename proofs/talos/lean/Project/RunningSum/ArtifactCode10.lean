import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_10_32_t_tail17 :
    instructionSequenceAt 202 false { bytes := bytes, pos := 15749, limit := 15890 } =
      .ok ((((((raw.core.codes[10]!).body)[32]!).childBody false).drop 17, .end), { bytes := bytes, pos := 15888, limit := 15890 }) := by
  cbv

@[cbv_eval] theorem sequence_10_32_t_tail0 :
    instructionSequenceAt 219 false { bytes := bytes, pos := 15717, limit := 15890 } =
      .ok ((((((raw.core.codes[10]!).body)[32]!).childBody false).drop 0, .end), { bytes := bytes, pos := 15888, limit := 15890 }) := by
  cbv

@[cbv_eval] theorem sequence_10_tail32 :
    instructionSequenceAt 221 false { bytes := bytes, pos := 15715, limit := 15890 } =
      .ok ((((raw.core.codes[10]!).body).drop 32, .end), { bytes := bytes, pos := 15890, limit := 15890 }) := by
  cbv

@[cbv_eval] theorem sequence_10_tail0 :
    instructionSequenceAt 253 false { bytes := bytes, pos := 15637, limit := 15890 } =
      .ok ((((raw.core.codes[10]!).body).drop 0, .end), { bytes := bytes, pos := 15890, limit := 15890 }) := by
  cbv

theorem code10_decoded :
    code { bytes := bytes, pos := 15632, limit := 16553 } = .ok (raw.core.codes[10]!, { bytes := bytes, pos := 15890, limit := 16553 }) := by
  refine code_eq_of_parts (size := 256)
    (payload := { bytes := bytes, pos := 15634, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 15637, limit := 15890 })
    (bodyFinish := { bytes := bytes, pos := 15890, limit := 15890 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_10_tail0
  · rfl

#print axioms code10_decoded

end Project.RunningSum.Artifact
