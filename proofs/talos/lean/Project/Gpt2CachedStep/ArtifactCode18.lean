import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_18_12_t_0_t_tail21 :
    instructionSequenceAt 189 false { bytes := artifactBytes, pos := 1507, limit := 1664 } =
      .ok ((((((((Cache.raw.codes[18]!).body)[12]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 1635, limit := 1664 }) := by
  cbv

@[cbv_eval] theorem sequence_18_12_t_0_t_tail0 :
    instructionSequenceAt 210 false { bytes := artifactBytes, pos := 1467, limit := 1664 } =
      .ok ((((((((Cache.raw.codes[18]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1635, limit := 1664 }) := by
  cbv

@[cbv_eval] theorem sequence_18_12_t_tail0 :
    instructionSequenceAt 212 false { bytes := artifactBytes, pos := 1465, limit := 1664 } =
      .ok ((((((Cache.raw.codes[18]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1636, limit := 1664 }) := by
  cbv

@[cbv_eval] theorem sequence_18_tail12 :
    instructionSequenceAt 214 false { bytes := artifactBytes, pos := 1463, limit := 1664 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 12, .end), { bytes := artifactBytes, pos := 1664, limit := 1664 }) := by
  cbv

@[cbv_eval] theorem sequence_18_tail0 :
    instructionSequenceAt 226 false { bytes := artifactBytes, pos := 1438, limit := 1664 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1664, limit := 1664 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 1433, limit := 19083 } = .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 1664, limit := 19083 }) := by
  refine code_eq_of_parts (size := 229)
    (payload := { bytes := artifactBytes, pos := 1435, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 1438, limit := 1664 })
    (bodyFinish := { bytes := artifactBytes, pos := 1664, limit := 1664 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_18_tail0
  · rfl

#print axioms code18_decoded

end Project.Gpt2CachedStep.Artifact
