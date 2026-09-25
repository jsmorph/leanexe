import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_tail0 :
    instructionSequenceAt 99 false { bytes := artifactBytes, pos := 739, limit := 838 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 838, limit := 838 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 735, limit := 4741 } = .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 838, limit := 4741 }) := by
  refine code_eq_of_parts (size := 102)
    (payload := { bytes := artifactBytes, pos := 736, limit := 4741 })
    (bodyStart := { bytes := artifactBytes, pos := 739, limit := 838 })
    (bodyFinish := { bytes := artifactBytes, pos := 838, limit := 838 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_2_tail0
  · rfl

#print axioms code2_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
