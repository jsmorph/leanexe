import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_52_9_e_tail31 :
    instructionSequenceAt 185 false { bytes := artifactBytes, pos := 20168, limit := 20299 } =
      .ok ((((((Cache.raw.codes[52]!).body)[9]!).childBody true).drop 31, .end), { bytes := artifactBytes, pos := 20296, limit := 20299 }) := by
  cbv

@[cbv_eval] theorem sequence_52_9_e_tail0 :
    instructionSequenceAt 216 false { bytes := artifactBytes, pos := 20121, limit := 20299 } =
      .ok ((((((Cache.raw.codes[52]!).body)[9]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 20296, limit := 20299 }) := by
  cbv

@[cbv_eval] theorem sequence_52_tail9 :
    instructionSequenceAt 218 false { bytes := artifactBytes, pos := 20099, limit := 20299 } =
      .ok ((((Cache.raw.codes[52]!).body).drop 9, .end), { bytes := artifactBytes, pos := 20299, limit := 20299 }) := by
  cbv

@[cbv_eval] theorem sequence_52_tail0 :
    instructionSequenceAt 227 false { bytes := artifactBytes, pos := 20072, limit := 20299 } =
      .ok ((((Cache.raw.codes[52]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20299, limit := 20299 }) := by
  cbv

theorem code52_decoded :
    code { bytes := artifactBytes, pos := 20067, limit := 28315 } = .ok (Cache.raw.codes[52]!, { bytes := artifactBytes, pos := 20299, limit := 28315 }) := by
  refine code_eq_of_parts (size := 230)
    (payload := { bytes := artifactBytes, pos := 20069, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 20072, limit := 20299 })
    (bodyFinish := { bytes := artifactBytes, pos := 20299, limit := 20299 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_52_tail0
  · rfl

#print axioms code52_decoded

end Project.Gpt2QuantizedCached.Artifact
