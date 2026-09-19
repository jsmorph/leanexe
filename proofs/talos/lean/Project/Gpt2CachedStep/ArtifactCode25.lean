import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_25_33_t_0_t_tail74 :
    instructionSequenceAt 328 false { bytes := artifactBytes, pos := 6107, limit := 6268 } =
      .ok ((((((((Cache.raw.codes[25]!).body)[33]!).childBody false)[0]!).childBody false).drop 74, .end), { bytes := artifactBytes, pos := 6252, limit := 6268 }) := by
  cbv

@[cbv_eval] theorem sequence_25_33_t_0_t_tail21 :
    instructionSequenceAt 381 false { bytes := artifactBytes, pos := 5960, limit := 6268 } =
      .ok ((((((((Cache.raw.codes[25]!).body)[33]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 6252, limit := 6268 }) := by
  cbv

@[cbv_eval] theorem sequence_25_33_t_0_t_tail0 :
    instructionSequenceAt 402 false { bytes := artifactBytes, pos := 5920, limit := 6268 } =
      .ok ((((((((Cache.raw.codes[25]!).body)[33]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6252, limit := 6268 }) := by
  cbv

@[cbv_eval] theorem sequence_25_33_t_tail0 :
    instructionSequenceAt 404 false { bytes := artifactBytes, pos := 5918, limit := 6268 } =
      .ok ((((((Cache.raw.codes[25]!).body)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6253, limit := 6268 }) := by
  cbv

@[cbv_eval] theorem sequence_25_tail33 :
    instructionSequenceAt 406 false { bytes := artifactBytes, pos := 5916, limit := 6268 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 33, .end), { bytes := artifactBytes, pos := 6268, limit := 6268 }) := by
  cbv

@[cbv_eval] theorem sequence_25_tail0 :
    instructionSequenceAt 439 false { bytes := artifactBytes, pos := 5829, limit := 6268 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6268, limit := 6268 }) := by
  cbv

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 5824, limit := 19083 } = .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 6268, limit := 19083 }) := by
  refine code_eq_of_parts (size := 442)
    (payload := { bytes := artifactBytes, pos := 5826, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 5829, limit := 6268 })
    (bodyFinish := { bytes := artifactBytes, pos := 6268, limit := 6268 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_25_tail0
  · rfl

#print axioms code25_decoded

end Project.Gpt2CachedStep.Artifact
