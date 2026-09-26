import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode0Sequences0

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_38_e_tail61 :
    instructionSequenceAt 1139 false { bytes := bytes, pos := 1537, limit := 1719 } =
      .ok ((((((raw.core.codes[0]!).body)[38]!).childBody true).drop 61, .end), { bytes := bytes, pos := 1708, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_38_e_tail24 :
    instructionSequenceAt 1176 false { bytes := bytes, pos := 861, limit := 1719 } =
      .ok ((((((raw.core.codes[0]!).body)[38]!).childBody true).drop 24, .end), { bytes := bytes, pos := 1708, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_38_e_tail0 :
    instructionSequenceAt 1200 false { bytes := bytes, pos := 813, limit := 1719 } =
      .ok ((((((raw.core.codes[0]!).body)[38]!).childBody true).drop 0, .end), { bytes := bytes, pos := 1708, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail38 :
    instructionSequenceAt 1202 false { bytes := bytes, pos := 790, limit := 1719 } =
      .ok ((((raw.core.codes[0]!).body).drop 38, .end), { bytes := bytes, pos := 1719, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail16 :
    instructionSequenceAt 1224 false { bytes := bytes, pos := 619, limit := 1719 } =
      .ok ((((raw.core.codes[0]!).body).drop 16, .end), { bytes := bytes, pos := 1719, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail3 :
    instructionSequenceAt 1237 false { bytes := bytes, pos := 484, limit := 1719 } =
      .ok ((((raw.core.codes[0]!).body).drop 3, .end), { bytes := bytes, pos := 1719, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail0 :
    instructionSequenceAt 1240 false { bytes := bytes, pos := 479, limit := 1719 } =
      .ok ((((raw.core.codes[0]!).body).drop 0, .end), { bytes := bytes, pos := 1719, limit := 1719 }) := by
  cbv


end Project.RunningSum.Artifact
