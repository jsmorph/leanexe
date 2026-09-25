import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_13_tail64 :
    instructionSequenceAt 232 false { bytes := bytes, pos := 16341, limit := 16469 } =
      .ok ((((raw.core.codes[13]!).body).drop 64, .end), { bytes := bytes, pos := 16469, limit := 16469 }) := by
  cbv

@[cbv_eval] theorem sequence_13_tail15 :
    instructionSequenceAt 281 false { bytes := bytes, pos := 16212, limit := 16469 } =
      .ok ((((raw.core.codes[13]!).body).drop 15, .end), { bytes := bytes, pos := 16469, limit := 16469 }) := by
  cbv

@[cbv_eval] theorem sequence_13_tail0 :
    instructionSequenceAt 296 false { bytes := bytes, pos := 16173, limit := 16469 } =
      .ok ((((raw.core.codes[13]!).body).drop 0, .end), { bytes := bytes, pos := 16469, limit := 16469 }) := by
  cbv

theorem code13_decoded :
    code { bytes := bytes, pos := 16168, limit := 16469 } = .ok (raw.core.codes[13]!, { bytes := bytes, pos := 16469, limit := 16469 }) := by
  refine code_eq_of_parts (size := 299)
    (payload := { bytes := bytes, pos := 16170, limit := 16469 })
    (bodyStart := { bytes := bytes, pos := 16173, limit := 16469 })
    (bodyFinish := { bytes := bytes, pos := 16469, limit := 16469 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_13_tail0
  · rfl

#print axioms code13_decoded

end Project.RunningSum.Artifact
