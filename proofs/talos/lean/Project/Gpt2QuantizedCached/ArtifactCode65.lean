import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_65_tail43 :
    instructionSequenceAt 305 false { bytes := artifactBytes, pos := 27857, limit := 28017 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 43, .end), { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  cbv

@[cbv_eval] theorem sequence_65_tail25 :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 27728, limit := 28017 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 25, .end), { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  cbv

@[cbv_eval] theorem sequence_65_tail0 :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 27669, limit := 28017 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 0, .end), { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  cbv

theorem code65_decoded :
    code { bytes := artifactBytes, pos := 27664, limit := 28017 } = .ok (Cache.raw.codes[65]!, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 27666, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 27669, limit := 28017 })
    (bodyFinish := { bytes := artifactBytes, pos := 28017, limit := 28017 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_65_tail0
  · rfl

#print axioms code65_decoded

end Project.Gpt2QuantizedCached.Artifact
