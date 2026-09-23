import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_61_tail0 :
    instructionSequenceAt 50 false { bytes := artifactBytes, pos := 27436, limit := 27486 } =
      .ok ((((Cache.raw.codes[61]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27486, limit := 27486 }) := by
  cbv

theorem code61_decoded :
    code { bytes := artifactBytes, pos := 27432, limit := 28315 } = .ok (Cache.raw.codes[61]!, { bytes := artifactBytes, pos := 27486, limit := 28315 }) := by
  refine code_eq_of_parts (size := 53)
    (payload := { bytes := artifactBytes, pos := 27433, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 27436, limit := 27486 })
    (bodyFinish := { bytes := artifactBytes, pos := 27486, limit := 27486 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_61_tail0
  · rfl

#print axioms code61_decoded

end Project.Gpt2QuantizedCached.Artifact
