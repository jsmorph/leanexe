import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_4_12_t_0_t_tail38 :
    instructionSequenceAt 206 false { bytes := artifactBytes, pos := 2129, limit := 2274 } =
      .ok ((((((((Cache.raw.codes[4]!).body)[12]!).childBody false)[0]!).childBody false).drop 38, .end), { bytes := artifactBytes, pos := 2258, limit := 2274 }) := by
  cbv

@[cbv_eval] theorem sequence_4_12_t_0_t_tail0 :
    instructionSequenceAt 244 false { bytes := artifactBytes, pos := 2042, limit := 2274 } =
      .ok ((((((((Cache.raw.codes[4]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2258, limit := 2274 }) := by
  cbv

@[cbv_eval] theorem sequence_4_12_t_tail0 :
    instructionSequenceAt 246 false { bytes := artifactBytes, pos := 2040, limit := 2274 } =
      .ok ((((((Cache.raw.codes[4]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2259, limit := 2274 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail12 :
    instructionSequenceAt 248 false { bytes := artifactBytes, pos := 2038, limit := 2274 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 12, .end), { bytes := artifactBytes, pos := 2274, limit := 2274 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail0 :
    instructionSequenceAt 260 false { bytes := artifactBytes, pos := 2014, limit := 2274 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2274, limit := 2274 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 2009, limit := 5441 } = .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 2274, limit := 5441 }) := by
  refine code_eq_of_parts (size := 263)
    (payload := { bytes := artifactBytes, pos := 2011, limit := 5441 })
    (bodyStart := { bytes := artifactBytes, pos := 2014, limit := 2274 })
    (bodyFinish := { bytes := artifactBytes, pos := 2274, limit := 2274 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_4_tail0
  · rfl

#print axioms code4_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
