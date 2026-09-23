import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_1_12_t_0_t_tail39 :
    instructionSequenceAt 289 false { bytes := artifactBytes, pos := 512, limit := 743 } =
      .ok ((((((((Cache.raw.codes[1]!).body)[12]!).childBody false)[0]!).childBody false).drop 39, .end), { bytes := artifactBytes, pos := 653, limit := 743 }) := by
  cbv

@[cbv_eval] theorem sequence_1_12_t_0_t_tail0 :
    instructionSequenceAt 328 false { bytes := artifactBytes, pos := 427, limit := 743 } =
      .ok ((((((((Cache.raw.codes[1]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 653, limit := 743 }) := by
  cbv

@[cbv_eval] theorem sequence_1_12_t_tail0 :
    instructionSequenceAt 330 false { bytes := artifactBytes, pos := 425, limit := 743 } =
      .ok ((((((Cache.raw.codes[1]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 654, limit := 743 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail12 :
    instructionSequenceAt 332 false { bytes := artifactBytes, pos := 423, limit := 743 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 12, .end), { bytes := artifactBytes, pos := 743, limit := 743 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail0 :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 399, limit := 743 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 743, limit := 743 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 394, limit := 4757 } = .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 743, limit := 4757 }) := by
  refine code_eq_of_parts (size := 347)
    (payload := { bytes := artifactBytes, pos := 396, limit := 4757 })
    (bodyStart := { bytes := artifactBytes, pos := 399, limit := 743 })
    (bodyFinish := { bytes := artifactBytes, pos := 743, limit := 743 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_1_tail0
  · rfl

#print axioms code1_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
