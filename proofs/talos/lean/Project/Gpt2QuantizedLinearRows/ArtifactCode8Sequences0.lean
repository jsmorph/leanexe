import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_83_t_0_t_19_t_tail136 :
    instructionSequenceAt 1329 true { bytes := artifactBytes, pos := 3290, limit := 3912 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 136, .otherwise), { bytes := artifactBytes, pos := 3419, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_t_tail99 :
    instructionSequenceAt 1366 true { bytes := artifactBytes, pos := 3161, limit := 3912 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 99, .otherwise), { bytes := artifactBytes, pos := 3419, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_t_tail49 :
    instructionSequenceAt 1416 true { bytes := artifactBytes, pos := 3032, limit := 3912 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 49, .otherwise), { bytes := artifactBytes, pos := 3419, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_t_tail5 :
    instructionSequenceAt 1460 true { bytes := artifactBytes, pos := 2904, limit := 3912 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 5, .otherwise), { bytes := artifactBytes, pos := 3419, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_t_tail0 :
    instructionSequenceAt 1465 true { bytes := artifactBytes, pos := 2894, limit := 3912 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3419, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_e_tail98 :
    instructionSequenceAt 1367 false { bytes := artifactBytes, pos := 3684, limit := 3912 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 98, .end), { bytes := artifactBytes, pos := 3812, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_e_tail48 :
    instructionSequenceAt 1417 false { bytes := artifactBytes, pos := 3555, limit := 3912 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 48, .end), { bytes := artifactBytes, pos := 3812, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_e_tail4 :
    instructionSequenceAt 1461 false { bytes := artifactBytes, pos := 3427, limit := 3912 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 4, .end), { bytes := artifactBytes, pos := 3812, limit := 3912 }) := by
  cbv


end Project.Gpt2QuantizedLinearRows.Artifact
