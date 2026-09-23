import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_tail0 :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 2294, limit := 2327 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2327, limit := 2327 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 2290, limit := 4757 } = .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 2327, limit := 4757 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 2291, limit := 4757 })
    (bodyStart := { bytes := artifactBytes, pos := 2294, limit := 2327 })
    (bodyFinish := { bytes := artifactBytes, pos := 2327, limit := 2327 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_6_tail0
  · rfl

#print axioms code6_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
