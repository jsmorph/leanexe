import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_41_tail0 :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 11148, limit := 11167 } =
      .ok ((((Cache.raw.codes[41]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11167, limit := 11167 }) := by
  cbv

theorem code41_decoded :
    code { bytes := artifactBytes, pos := 11144, limit := 28017 } = .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 11167, limit := 28017 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 11145, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 11148, limit := 11167 })
    (bodyFinish := { bytes := artifactBytes, pos := 11167, limit := 11167 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_41_tail0
  · rfl

#print axioms code41_decoded

end Project.Gpt2QuantizedCached.Artifact
