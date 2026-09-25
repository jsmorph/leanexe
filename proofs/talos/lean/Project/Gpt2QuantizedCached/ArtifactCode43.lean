import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_43_3_t_tail11 :
    instructionSequenceAt 201 true { bytes := artifactBytes, pos := 13442, limit := 13630 } =
      .ok ((((((Cache.raw.codes[43]!).body)[3]!).childBody false).drop 11, .otherwise), { bytes := artifactBytes, pos := 13570, limit := 13630 }) := by
  cbv

@[cbv_eval] theorem sequence_43_3_t_tail0 :
    instructionSequenceAt 212 true { bytes := artifactBytes, pos := 13420, limit := 13630 } =
      .ok ((((((Cache.raw.codes[43]!).body)[3]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 13570, limit := 13630 }) := by
  cbv

@[cbv_eval] theorem sequence_43_tail3 :
    instructionSequenceAt 214 false { bytes := artifactBytes, pos := 13418, limit := 13630 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 3, .end), { bytes := artifactBytes, pos := 13630, limit := 13630 }) := by
  cbv

@[cbv_eval] theorem sequence_43_tail0 :
    instructionSequenceAt 217 false { bytes := artifactBytes, pos := 13413, limit := 13630 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13630, limit := 13630 }) := by
  cbv

theorem code43_decoded :
    code { bytes := artifactBytes, pos := 13408, limit := 28017 } = .ok (Cache.raw.codes[43]!, { bytes := artifactBytes, pos := 13630, limit := 28017 }) := by
  refine code_eq_of_parts (size := 220)
    (payload := { bytes := artifactBytes, pos := 13410, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 13413, limit := 13630 })
    (bodyFinish := { bytes := artifactBytes, pos := 13630, limit := 13630 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_43_tail0
  · rfl

#print axioms code43_decoded

end Project.Gpt2QuantizedCached.Artifact
