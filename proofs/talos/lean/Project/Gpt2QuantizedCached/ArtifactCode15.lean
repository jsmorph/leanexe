import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_15_tail0 :
    instructionSequenceAt 66 false { bytes := artifactBytes, pos := 1744, limit := 1810 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1810, limit := 1810 }) := by
  cbv

theorem code15_decoded :
    code { bytes := artifactBytes, pos := 1740, limit := 28315 } = .ok (Cache.raw.codes[15]!, { bytes := artifactBytes, pos := 1810, limit := 28315 }) := by
  refine code_eq_of_parts (size := 69)
    (payload := { bytes := artifactBytes, pos := 1741, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 1744, limit := 1810 })
    (bodyFinish := { bytes := artifactBytes, pos := 1810, limit := 1810 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_15_tail0
  · rfl

#print axioms code15_decoded

end Project.Gpt2QuantizedCached.Artifact
