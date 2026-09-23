import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_14_tail0 :
    instructionSequenceAt 67 false { bytes := artifactBytes, pos := 1673, limit := 1740 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1740, limit := 1740 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 1669, limit := 28315 } = .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 1740, limit := 28315 }) := by
  refine code_eq_of_parts (size := 70)
    (payload := { bytes := artifactBytes, pos := 1670, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 1673, limit := 1740 })
    (bodyFinish := { bytes := artifactBytes, pos := 1740, limit := 1740 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_14_tail0
  · rfl

#print axioms code14_decoded

end Project.Gpt2QuantizedCached.Artifact
