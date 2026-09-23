import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_5_tail0 :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 2271, limit := 2290 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2290, limit := 2290 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 2267, limit := 4757 } = .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 2290, limit := 4757 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 2268, limit := 4757 })
    (bodyStart := { bytes := artifactBytes, pos := 2271, limit := 2290 })
    (bodyFinish := { bytes := artifactBytes, pos := 2290, limit := 2290 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_5_tail0
  · rfl

#print axioms code5_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
