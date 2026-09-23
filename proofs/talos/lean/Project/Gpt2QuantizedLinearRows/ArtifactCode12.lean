import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_12_tail43 :
    instructionSequenceAt 305 false { bytes := artifactBytes, pos := 4597, limit := 4757 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 43, .end), { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  cbv

@[cbv_eval] theorem sequence_12_tail25 :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 4468, limit := 4757 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 25, .end), { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  cbv

@[cbv_eval] theorem sequence_12_tail0 :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 4409, limit := 4757 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 4404, limit := 4757 } = .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 4406, limit := 4757 })
    (bodyStart := { bytes := artifactBytes, pos := 4409, limit := 4757 })
    (bodyFinish := { bytes := artifactBytes, pos := 4757, limit := 4757 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_12_tail0
  · rfl

#print axioms code12_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
