import Project.ByteIO.ArtifactByteLookup
import Project.ByteIO.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ByteIO.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_tail0 :
    instructionSequenceAt 7 false { bytes := bytes, pos := 1421, limit := 1428 } =
      .ok ((((raw.core.codes[3]!).body).drop 0, .end), { bytes := bytes, pos := 1428, limit := 1428 }) := by
  cbv

theorem code3_decoded :
    code { bytes := bytes, pos := 1419, limit := 2082 } = .ok (raw.core.codes[3]!, { bytes := bytes, pos := 1428, limit := 2082 }) := by
  refine code_eq_of_parts (size := 8)
    (payload := { bytes := bytes, pos := 1420, limit := 2082 })
    (bodyStart := { bytes := bytes, pos := 1421, limit := 1428 })
    (bodyFinish := { bytes := bytes, pos := 1428, limit := 1428 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_3_tail0
  · rfl

#print axioms code3_decoded

end Project.ByteIO.Artifact
