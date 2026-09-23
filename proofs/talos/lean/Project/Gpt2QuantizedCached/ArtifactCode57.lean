import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_57_tail0 :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 23791, limit := 23810 } =
      .ok ((((Cache.raw.codes[57]!).body).drop 0, .end), { bytes := artifactBytes, pos := 23810, limit := 23810 }) := by
  cbv

theorem code57_decoded :
    code { bytes := artifactBytes, pos := 23787, limit := 28315 } = .ok (Cache.raw.codes[57]!, { bytes := artifactBytes, pos := 23810, limit := 28315 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 23788, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 23791, limit := 23810 })
    (bodyFinish := { bytes := artifactBytes, pos := 23810, limit := 23810 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_57_tail0
  · rfl

#print axioms code57_decoded

end Project.Gpt2QuantizedCached.Artifact
