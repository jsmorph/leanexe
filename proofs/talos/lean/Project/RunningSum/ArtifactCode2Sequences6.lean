import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode2Sequences5

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_55_t_tail69 :
    instructionSequenceAt 3769 true { bytes := bytes, pos := 3366, limit := 5631 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody false).drop 69, .otherwise), { bytes := bytes, pos := 4491, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_tail40 :
    instructionSequenceAt 3798 true { bytes := bytes, pos := 3116, limit := 5631 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody false).drop 40, .otherwise), { bytes := bytes, pos := 4491, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_tail36 :
    instructionSequenceAt 3802 true { bytes := bytes, pos := 2937, limit := 5631 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody false).drop 36, .otherwise), { bytes := bytes, pos := 4491, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_tail0 :
    instructionSequenceAt 3838 true { bytes := bytes, pos := 2864, limit := 5631 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody false).drop 0, .otherwise), { bytes := bytes, pos := 4491, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_tail29 :
    instructionSequenceAt 3809 false { bytes := bytes, pos := 4829, limit := 5631 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody true).drop 29, .end), { bytes := bytes, pos := 5598, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_tail4 :
    instructionSequenceAt 3834 false { bytes := bytes, pos := 4499, limit := 5631 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody true).drop 4, .end), { bytes := bytes, pos := 5598, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_tail0 :
    instructionSequenceAt 3838 false { bytes := bytes, pos := 4491, limit := 5631 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody true).drop 0, .end), { bytes := bytes, pos := 5598, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_tail55 :
    instructionSequenceAt 3840 false { bytes := bytes, pos := 2862, limit := 5631 } =
      .ok ((((raw.core.codes[2]!).body).drop 55, .end), { bytes := bytes, pos := 5631, limit := 5631 }) := by
  cbv


end Project.RunningSum.Artifact
