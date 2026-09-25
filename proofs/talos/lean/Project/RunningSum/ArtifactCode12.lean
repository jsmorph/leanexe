import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_12_tail43 :
    instructionSequenceAt 305 false { bytes := bytes, pos := 16008, limit := 16168 } =
      .ok ((((raw.core.codes[12]!).body).drop 43, .end), { bytes := bytes, pos := 16168, limit := 16168 }) := by
  cbv

@[cbv_eval] theorem sequence_12_tail25 :
    instructionSequenceAt 323 false { bytes := bytes, pos := 15879, limit := 16168 } =
      .ok ((((raw.core.codes[12]!).body).drop 25, .end), { bytes := bytes, pos := 16168, limit := 16168 }) := by
  cbv

@[cbv_eval] theorem sequence_12_tail0 :
    instructionSequenceAt 348 false { bytes := bytes, pos := 15820, limit := 16168 } =
      .ok ((((raw.core.codes[12]!).body).drop 0, .end), { bytes := bytes, pos := 16168, limit := 16168 }) := by
  cbv

theorem code12_decoded :
    code { bytes := bytes, pos := 15815, limit := 16469 } = .ok (raw.core.codes[12]!, { bytes := bytes, pos := 16168, limit := 16469 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := bytes, pos := 15817, limit := 16469 })
    (bodyStart := { bytes := bytes, pos := 15820, limit := 16168 })
    (bodyFinish := { bytes := bytes, pos := 16168, limit := 16168 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_12_tail0
  · rfl

#print axioms code12_decoded

end Project.RunningSum.Artifact
