import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_29_tail0 :
    instructionSequenceAt 43 false { bytes := artifactBytes, pos := 5575, limit := 5618 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5618, limit := 5618 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 5571, limit := 28017 } = .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 5618, limit := 28017 }) := by
  refine code_eq_of_parts (size := 46)
    (payload := { bytes := artifactBytes, pos := 5572, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 5575, limit := 5618 })
    (bodyFinish := { bytes := artifactBytes, pos := 5618, limit := 5618 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_29_tail0
  · rfl

#print axioms code29_decoded

end Project.Gpt2QuantizedCached.Artifact
