import Project.ByteIO.ArtifactByteLookup
import Project.ByteIO.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ByteIO.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_4_tail43 :
    instructionSequenceAt 305 false { bytes := bytes, pos := 1621, limit := 1781 } =
      .ok ((((raw.core.codes[4]!).body).drop 43, .end), { bytes := bytes, pos := 1781, limit := 1781 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail25 :
    instructionSequenceAt 323 false { bytes := bytes, pos := 1492, limit := 1781 } =
      .ok ((((raw.core.codes[4]!).body).drop 25, .end), { bytes := bytes, pos := 1781, limit := 1781 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail0 :
    instructionSequenceAt 348 false { bytes := bytes, pos := 1433, limit := 1781 } =
      .ok ((((raw.core.codes[4]!).body).drop 0, .end), { bytes := bytes, pos := 1781, limit := 1781 }) := by
  cbv

theorem code4_decoded :
    code { bytes := bytes, pos := 1428, limit := 2082 } = .ok (raw.core.codes[4]!, { bytes := bytes, pos := 1781, limit := 2082 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := bytes, pos := 1430, limit := 2082 })
    (bodyStart := { bytes := bytes, pos := 1433, limit := 1781 })
    (bodyFinish := { bytes := bytes, pos := 1781, limit := 1781 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_4_tail0
  · rfl

#print axioms code4_decoded

end Project.ByteIO.Artifact
