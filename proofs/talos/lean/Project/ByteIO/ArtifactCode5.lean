import Project.ByteIO.ArtifactByteLookup
import Project.ByteIO.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ByteIO.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_5_tail64 :
    instructionSequenceAt 232 false { bytes := bytes, pos := 1954, limit := 2082 } =
      .ok ((((raw.core.codes[5]!).body).drop 64, .end), { bytes := bytes, pos := 2082, limit := 2082 }) := by
  cbv

@[cbv_eval] theorem sequence_5_tail15 :
    instructionSequenceAt 281 false { bytes := bytes, pos := 1825, limit := 2082 } =
      .ok ((((raw.core.codes[5]!).body).drop 15, .end), { bytes := bytes, pos := 2082, limit := 2082 }) := by
  cbv

@[cbv_eval] theorem sequence_5_tail0 :
    instructionSequenceAt 296 false { bytes := bytes, pos := 1786, limit := 2082 } =
      .ok ((((raw.core.codes[5]!).body).drop 0, .end), { bytes := bytes, pos := 2082, limit := 2082 }) := by
  cbv

theorem code5_decoded :
    code { bytes := bytes, pos := 1781, limit := 2082 } = .ok (raw.core.codes[5]!, { bytes := bytes, pos := 2082, limit := 2082 }) := by
  refine code_eq_of_parts (size := 299)
    (payload := { bytes := bytes, pos := 1783, limit := 2082 })
    (bodyStart := { bytes := bytes, pos := 1786, limit := 2082 })
    (bodyFinish := { bytes := bytes, pos := 2082, limit := 2082 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_5_tail0
  · rfl

#print axioms code5_decoded

end Project.ByteIO.Artifact
