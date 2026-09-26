import Project.ByteIO.ArtifactByteLookup
import Project.ByteIO.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ByteIO.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_32_t_tail17 :
    instructionSequenceAt 202 false { bytes := bytes, pos := 1278, limit := 1419 } =
      .ok ((((((raw.core.codes[2]!).body)[32]!).childBody false).drop 17, .end), { bytes := bytes, pos := 1417, limit := 1419 }) := by
  cbv

@[cbv_eval] theorem sequence_2_32_t_tail0 :
    instructionSequenceAt 219 false { bytes := bytes, pos := 1246, limit := 1419 } =
      .ok ((((((raw.core.codes[2]!).body)[32]!).childBody false).drop 0, .end), { bytes := bytes, pos := 1417, limit := 1419 }) := by
  cbv

@[cbv_eval] theorem sequence_2_tail32 :
    instructionSequenceAt 221 false { bytes := bytes, pos := 1244, limit := 1419 } =
      .ok ((((raw.core.codes[2]!).body).drop 32, .end), { bytes := bytes, pos := 1419, limit := 1419 }) := by
  cbv

@[cbv_eval] theorem sequence_2_tail0 :
    instructionSequenceAt 253 false { bytes := bytes, pos := 1166, limit := 1419 } =
      .ok ((((raw.core.codes[2]!).body).drop 0, .end), { bytes := bytes, pos := 1419, limit := 1419 }) := by
  cbv

theorem code2_decoded :
    code { bytes := bytes, pos := 1161, limit := 2082 } = .ok (raw.core.codes[2]!, { bytes := bytes, pos := 1419, limit := 2082 }) := by
  refine code_eq_of_parts (size := 256)
    (payload := { bytes := bytes, pos := 1163, limit := 2082 })
    (bodyStart := { bytes := bytes, pos := 1166, limit := 1419 })
    (bodyFinish := { bytes := bytes, pos := 1419, limit := 1419 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_2_tail0
  · rfl

#print axioms code2_decoded

end Project.ByteIO.Artifact
