import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_tail0 :
    instructionSequenceAt 67 false { bytes := artifactBytes, pos := 887, limit := 954 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 954, limit := 954 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 883, limit := 28017 } = .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 954, limit := 28017 }) := by
  refine code_eq_of_parts (size := 70)
    (payload := { bytes := artifactBytes, pos := 884, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 887, limit := 954 })
    (bodyFinish := { bytes := artifactBytes, pos := 954, limit := 954 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_3_tail0
  · rfl

#print axioms code3_decoded

end Project.Gpt2QuantizedCached.Artifact
