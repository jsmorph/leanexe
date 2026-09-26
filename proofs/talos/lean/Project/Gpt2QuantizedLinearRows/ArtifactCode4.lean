import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_4_10_t_0_t_tail36 :
    instructionSequenceAt 202 false { bytes := artifactBytes, pos := 2106, limit := 2251 } =
      .ok ((((((((Cache.raw.codes[4]!).body)[10]!).childBody false)[0]!).childBody false).drop 36, .end), { bytes := artifactBytes, pos := 2235, limit := 2251 }) := by
  cbv

@[cbv_eval] theorem sequence_4_10_t_0_t_tail0 :
    instructionSequenceAt 238 false { bytes := artifactBytes, pos := 2023, limit := 2251 } =
      .ok ((((((((Cache.raw.codes[4]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2235, limit := 2251 }) := by
  cbv

@[cbv_eval] theorem sequence_4_10_t_tail0 :
    instructionSequenceAt 240 false { bytes := artifactBytes, pos := 2021, limit := 2251 } =
      .ok ((((((Cache.raw.codes[4]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2236, limit := 2251 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail10 :
    instructionSequenceAt 242 false { bytes := artifactBytes, pos := 2019, limit := 2251 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 10, .end), { bytes := artifactBytes, pos := 2251, limit := 2251 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail0 :
    instructionSequenceAt 252 false { bytes := artifactBytes, pos := 1999, limit := 2251 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2251, limit := 2251 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 1994, limit := 4741 } = .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 2251, limit := 4741 }) := by
  refine code_eq_of_parts (size := 255)
    (payload := { bytes := artifactBytes, pos := 1996, limit := 4741 })
    (bodyStart := { bytes := artifactBytes, pos := 1999, limit := 2251 })
    (bodyFinish := { bytes := artifactBytes, pos := 2251, limit := 2251 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_4_tail0
  · rfl

#print axioms code4_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
