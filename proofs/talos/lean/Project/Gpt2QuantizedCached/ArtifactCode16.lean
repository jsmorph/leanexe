import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_16_tail0 :
    instructionSequenceAt 66 false { bytes := artifactBytes, pos := 1814, limit := 1880 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1880, limit := 1880 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 1810, limit := 28315 } = .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 1880, limit := 28315 }) := by
  refine code_eq_of_parts (size := 69)
    (payload := { bytes := artifactBytes, pos := 1811, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 1814, limit := 1880 })
    (bodyFinish := { bytes := artifactBytes, pos := 1880, limit := 1880 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_16_tail0
  · rfl

#print axioms code16_decoded

end Project.Gpt2QuantizedCached.Artifact
