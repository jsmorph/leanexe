import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_36_t_0_t_tail18 :
    instructionSequenceAt 494 false { bytes := artifactBytes, pos := 11207, limit := 11622 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[36]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 11335, limit := 11622 }) := by
  cbv

@[cbv_eval] theorem sequence_30_36_t_0_t_tail0 :
    instructionSequenceAt 512 false { bytes := artifactBytes, pos := 11176, limit := 11622 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[36]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11335, limit := 11622 }) := by
  cbv

@[cbv_eval] theorem sequence_30_36_t_tail0 :
    instructionSequenceAt 514 false { bytes := artifactBytes, pos := 11174, limit := 11622 } =
      .ok ((((((Cache.raw.codes[30]!).body)[36]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11336, limit := 11622 }) := by
  cbv

@[cbv_eval] theorem sequence_30_40_t_tail8 :
    instructionSequenceAt 502 true { bytes := artifactBytes, pos := 11356, limit := 11622 } =
      .ok ((((((Cache.raw.codes[30]!).body)[40]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 11487, limit := 11622 }) := by
  cbv

@[cbv_eval] theorem sequence_30_40_t_tail0 :
    instructionSequenceAt 510 true { bytes := artifactBytes, pos := 11343, limit := 11622 } =
      .ok ((((((Cache.raw.codes[30]!).body)[40]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11487, limit := 11622 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail45 :
    instructionSequenceAt 507 false { bytes := artifactBytes, pos := 11494, limit := 11622 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 45, .end), { bytes := artifactBytes, pos := 11622, limit := 11622 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail40 :
    instructionSequenceAt 512 false { bytes := artifactBytes, pos := 11341, limit := 11622 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 40, .end), { bytes := artifactBytes, pos := 11622, limit := 11622 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail36 :
    instructionSequenceAt 516 false { bytes := artifactBytes, pos := 11172, limit := 11622 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 36, .end), { bytes := artifactBytes, pos := 11622, limit := 11622 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail0 :
    instructionSequenceAt 552 false { bytes := artifactBytes, pos := 11070, limit := 11622 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11622, limit := 11622 }) := by
  cbv

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 11065, limit := 19083 } = .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 11622, limit := 19083 }) := by
  refine code_eq_of_parts (size := 555)
    (payload := { bytes := artifactBytes, pos := 11067, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 11070, limit := 11622 })
    (bodyFinish := { bytes := artifactBytes, pos := 11622, limit := 11622 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_30_tail0
  · rfl

#print axioms code30_decoded

end Project.Gpt2CachedStep.Artifact
