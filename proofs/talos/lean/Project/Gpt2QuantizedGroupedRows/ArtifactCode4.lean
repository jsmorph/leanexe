import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_4_10_t_0_t_tail36 :
    instructionSequenceAt 202 false { bytes := artifactBytes, pos := 2113, limit := 2258 } =
      .ok ((((((((Cache.raw.codes[4]!).body)[10]!).childBody false)[0]!).childBody false).drop 36, .end), { bytes := artifactBytes, pos := 2242, limit := 2258 }) := by
  cbv

@[cbv_eval] theorem sequence_4_10_t_0_t_tail0 :
    instructionSequenceAt 238 false { bytes := artifactBytes, pos := 2030, limit := 2258 } =
      .ok ((((((((Cache.raw.codes[4]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2242, limit := 2258 }) := by
  cbv

@[cbv_eval] theorem sequence_4_10_t_tail0 :
    instructionSequenceAt 240 false { bytes := artifactBytes, pos := 2028, limit := 2258 } =
      .ok ((((((Cache.raw.codes[4]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2243, limit := 2258 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail10 :
    instructionSequenceAt 242 false { bytes := artifactBytes, pos := 2026, limit := 2258 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 10, .end), { bytes := artifactBytes, pos := 2258, limit := 2258 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail0 :
    instructionSequenceAt 252 false { bytes := artifactBytes, pos := 2006, limit := 2258 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2258, limit := 2258 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 2001, limit := 5409 } = .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 2258, limit := 5409 }) := by
  refine code_eq_of_parts (size := 255)
    (payload := { bytes := artifactBytes, pos := 2003, limit := 5409 })
    (bodyStart := { bytes := artifactBytes, pos := 2006, limit := 2258 })
    (bodyFinish := { bytes := artifactBytes, pos := 2258, limit := 2258 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_4_tail0
  · rfl

#print axioms code4_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
