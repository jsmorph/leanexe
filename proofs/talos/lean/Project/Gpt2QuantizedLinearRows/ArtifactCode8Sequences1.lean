import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedLinearRows.ArtifactCode8Sequences0

namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_83_t_0_t_19_e_tail0 :
    instructionSequenceAt 1465 false { bytes := artifactBytes, pos := 3419, limit := 3912 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 3812, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_70_t_0_t_tail18 :
    instructionSequenceAt 1481 false { bytes := artifactBytes, pos := 2557, limit := 3912 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[70]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 2685, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_70_t_0_t_tail0 :
    instructionSequenceAt 1499 false { bytes := artifactBytes, pos := 2526, limit := 3912 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[70]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2685, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_tail19 :
    instructionSequenceAt 1467 false { bytes := artifactBytes, pos := 2892, limit := 3912 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := artifactBytes, pos := 3826, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_tail0 :
    instructionSequenceAt 1486 false { bytes := artifactBytes, pos := 2856, limit := 3912 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3826, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_70_t_tail0 :
    instructionSequenceAt 1501 false { bytes := artifactBytes, pos := 2524, limit := 3912 } =
      .ok ((((((Cache.raw.codes[8]!).body)[70]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2686, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_74_t_tail8 :
    instructionSequenceAt 1489 true { bytes := artifactBytes, pos := 2706, limit := 3912 } =
      .ok ((((((Cache.raw.codes[8]!).body)[74]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 2837, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_74_t_tail0 :
    instructionSequenceAt 1497 true { bytes := artifactBytes, pos := 2693, limit := 3912 } =
      .ok ((((((Cache.raw.codes[8]!).body)[74]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2837, limit := 3912 }) := by
  cbv


end Project.Gpt2QuantizedLinearRows.Artifact
