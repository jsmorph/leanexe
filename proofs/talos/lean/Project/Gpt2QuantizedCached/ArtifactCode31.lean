import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_31_tail0 :
    instructionSequenceAt 85 false { bytes := artifactBytes, pos := 6535, limit := 6620 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6620, limit := 6620 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 6531, limit := 28315 } = .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 6620, limit := 28315 }) := by
  refine code_eq_of_parts (size := 88)
    (payload := { bytes := artifactBytes, pos := 6532, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 6535, limit := 6620 })
    (bodyFinish := { bytes := artifactBytes, pos := 6620, limit := 6620 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_31_tail0
  · rfl

#print axioms code31_decoded

end Project.Gpt2QuantizedCached.Artifact
