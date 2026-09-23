import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_10_tail0 :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 4297, limit := 4323 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4323, limit := 4323 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 4295, limit := 4757 } = .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 4323, limit := 4757 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 4296, limit := 4757 })
    (bodyStart := { bytes := artifactBytes, pos := 4297, limit := 4323 })
    (bodyFinish := { bytes := artifactBytes, pos := 4323, limit := 4323 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_10_tail0
  · rfl

#print axioms code10_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
