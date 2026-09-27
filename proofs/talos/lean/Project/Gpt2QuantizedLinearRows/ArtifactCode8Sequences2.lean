import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedLinearRows.ArtifactCode8Sequences1

namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_83_t_tail0 :
    instructionSequenceAt 1488 false { bytes := artifactBytes, pos := 2854, limit := 3912 } =
      .ok ((((((Cache.raw.codes[8]!).body)[83]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3827, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail83 :
    instructionSequenceAt 1490 false { bytes := artifactBytes, pos := 2852, limit := 3912 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 83, .end), { bytes := artifactBytes, pos := 3912, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail74 :
    instructionSequenceAt 1499 false { bytes := artifactBytes, pos := 2691, limit := 3912 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 74, .end), { bytes := artifactBytes, pos := 3912, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail70 :
    instructionSequenceAt 1503 false { bytes := artifactBytes, pos := 2522, limit := 3912 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 70, .end), { bytes := artifactBytes, pos := 3912, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail27 :
    instructionSequenceAt 1546 false { bytes := artifactBytes, pos := 2393, limit := 3912 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 27, .end), { bytes := artifactBytes, pos := 3912, limit := 3912 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail0 :
    instructionSequenceAt 1573 false { bytes := artifactBytes, pos := 2339, limit := 3912 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3912, limit := 3912 }) := by
  cbv


end Project.Gpt2QuantizedLinearRows.Artifact
