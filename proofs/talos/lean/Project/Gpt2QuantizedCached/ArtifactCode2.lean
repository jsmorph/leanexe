import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_tail0 :
    instructionSequenceAt 68 false { bytes := artifactBytes, pos := 815, limit := 883 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 883, limit := 883 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 811, limit := 28017 } = .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 883, limit := 28017 }) := by
  refine code_eq_of_parts (size := 71)
    (payload := { bytes := artifactBytes, pos := 812, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 815, limit := 883 })
    (bodyFinish := { bytes := artifactBytes, pos := 883, limit := 883 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_2_tail0
  · rfl

#print axioms code2_decoded

end Project.Gpt2QuantizedCached.Artifact
