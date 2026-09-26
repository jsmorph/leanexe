import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_63_tail0 :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 27557, limit := 27583 } =
      .ok ((((Cache.raw.codes[63]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27583, limit := 27583 }) := by
  cbv

theorem code63_decoded :
    code { bytes := artifactBytes, pos := 27555, limit := 28017 } = .ok (Cache.raw.codes[63]!, { bytes := artifactBytes, pos := 27583, limit := 28017 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 27556, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 27557, limit := 27583 })
    (bodyFinish := { bytes := artifactBytes, pos := 27583, limit := 27583 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_63_tail0
  · rfl

#print axioms code63_decoded

end Project.Gpt2QuantizedCached.Artifact
