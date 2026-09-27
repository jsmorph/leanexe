import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_31_9_e_tail31 :
    instructionSequenceAt 185 false { bytes := artifactBytes, pos := 11723, limit := 11854 } =
      .ok ((((((Cache.raw.codes[31]!).body)[9]!).childBody true).drop 31, .end), { bytes := artifactBytes, pos := 11851, limit := 11854 }) := by
  cbv

@[cbv_eval] theorem sequence_31_9_e_tail0 :
    instructionSequenceAt 216 false { bytes := artifactBytes, pos := 11676, limit := 11854 } =
      .ok ((((((Cache.raw.codes[31]!).body)[9]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 11851, limit := 11854 }) := by
  cbv

@[cbv_eval] theorem sequence_31_tail9 :
    instructionSequenceAt 218 false { bytes := artifactBytes, pos := 11654, limit := 11854 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 9, .end), { bytes := artifactBytes, pos := 11854, limit := 11854 }) := by
  cbv

@[cbv_eval] theorem sequence_31_tail0 :
    instructionSequenceAt 227 false { bytes := artifactBytes, pos := 11627, limit := 11854 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11854, limit := 11854 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 11622, limit := 19083 } = .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 11854, limit := 19083 }) := by
  refine code_eq_of_parts (size := 230)
    (payload := { bytes := artifactBytes, pos := 11624, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 11627, limit := 11854 })
    (bodyFinish := { bytes := artifactBytes, pos := 11854, limit := 11854 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_31_tail0
  · rfl

#print axioms code31_decoded

end Project.Gpt2CachedStep.Artifact
