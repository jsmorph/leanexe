import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_45_tail11 :
    instructionSequenceAt 160 false { bytes := artifactBytes, pos := 14129, limit := 14269 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 11, .end), { bytes := artifactBytes, pos := 14269, limit := 14269 }) := by
  cbv

@[cbv_eval] theorem sequence_45_tail0 :
    instructionSequenceAt 171 false { bytes := artifactBytes, pos := 14098, limit := 14269 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14269, limit := 14269 }) := by
  cbv

theorem code45_decoded :
    code { bytes := artifactBytes, pos := 14093, limit := 28315 } = .ok (Cache.raw.codes[45]!, { bytes := artifactBytes, pos := 14269, limit := 28315 }) := by
  refine code_eq_of_parts (size := 174)
    (payload := { bytes := artifactBytes, pos := 14095, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 14098, limit := 14269 })
    (bodyFinish := { bytes := artifactBytes, pos := 14269, limit := 14269 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_45_tail0
  · rfl

#print axioms code45_decoded

end Project.Gpt2QuantizedCached.Artifact
