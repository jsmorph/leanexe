import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_36_tail0 :
    instructionSequenceAt 99 false { bytes := artifactBytes, pos := 9572, limit := 9671 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9671, limit := 9671 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 9568, limit := 28017 } = .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 9671, limit := 28017 }) := by
  refine code_eq_of_parts (size := 102)
    (payload := { bytes := artifactBytes, pos := 9569, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 9572, limit := 9671 })
    (bodyFinish := { bytes := artifactBytes, pos := 9671, limit := 9671 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_36_tail0
  · rfl

#print axioms code36_decoded

end Project.Gpt2QuantizedCached.Artifact
