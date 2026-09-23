import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_7_tail0 :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 2331, limit := 2350 } =
      .ok ((((Cache.raw.codes[7]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2350, limit := 2350 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 2327, limit := 4757 } = .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 2350, limit := 4757 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 2328, limit := 4757 })
    (bodyStart := { bytes := artifactBytes, pos := 2331, limit := 2350 })
    (bodyFinish := { bytes := artifactBytes, pos := 2350, limit := 2350 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_7_tail0
  · rfl

#print axioms code7_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
