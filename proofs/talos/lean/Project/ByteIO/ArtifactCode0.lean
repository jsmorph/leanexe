import Project.ByteIO.ArtifactByteLookup
import Project.ByteIO.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ByteIO.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail0 :
    instructionSequenceAt 114 false { bytes := bytes, pos := 376, limit := 490 } =
      .ok ((((raw.core.codes[0]!).body).drop 0, .end), { bytes := bytes, pos := 490, limit := 490 }) := by
  cbv

theorem code0_decoded :
    code { bytes := bytes, pos := 372, limit := 2082 } = .ok (raw.core.codes[0]!, { bytes := bytes, pos := 490, limit := 2082 }) := by
  refine code_eq_of_parts (size := 117)
    (payload := { bytes := bytes, pos := 373, limit := 2082 })
    (bodyStart := { bytes := bytes, pos := 376, limit := 490 })
    (bodyFinish := { bytes := bytes, pos := 490, limit := 490 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_0_tail0
  · rfl

#print axioms code0_decoded

end Project.ByteIO.Artifact
