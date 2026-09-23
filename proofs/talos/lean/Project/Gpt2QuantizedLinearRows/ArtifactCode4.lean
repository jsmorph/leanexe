import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_4_12_t_0_t_tail38 :
    instructionSequenceAt 206 false { bytes := artifactBytes, pos := 2122, limit := 2267 } =
      .ok ((((((((Cache.raw.codes[4]!).body)[12]!).childBody false)[0]!).childBody false).drop 38, .end), { bytes := artifactBytes, pos := 2251, limit := 2267 }) := by
  cbv

@[cbv_eval] theorem sequence_4_12_t_0_t_tail0 :
    instructionSequenceAt 244 false { bytes := artifactBytes, pos := 2035, limit := 2267 } =
      .ok ((((((((Cache.raw.codes[4]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2251, limit := 2267 }) := by
  cbv

@[cbv_eval] theorem sequence_4_12_t_tail0 :
    instructionSequenceAt 246 false { bytes := artifactBytes, pos := 2033, limit := 2267 } =
      .ok ((((((Cache.raw.codes[4]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2252, limit := 2267 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail12 :
    instructionSequenceAt 248 false { bytes := artifactBytes, pos := 2031, limit := 2267 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 12, .end), { bytes := artifactBytes, pos := 2267, limit := 2267 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail0 :
    instructionSequenceAt 260 false { bytes := artifactBytes, pos := 2007, limit := 2267 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2267, limit := 2267 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 2002, limit := 4757 } = .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 2267, limit := 4757 }) := by
  refine code_eq_of_parts (size := 263)
    (payload := { bytes := artifactBytes, pos := 2004, limit := 4757 })
    (bodyStart := { bytes := artifactBytes, pos := 2007, limit := 2267 })
    (bodyFinish := { bytes := artifactBytes, pos := 2267, limit := 2267 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_4_tail0
  · rfl

#print axioms code4_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
