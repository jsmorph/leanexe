import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes112To119Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code115_seq_115_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 25655, limit := 25680 } =
      .ok ((((Cache.raw.codes[115]!).body).drop 0, .end), { bytes := artifactBytes, pos := 25680, limit := 25680 }) := by
  cbv

theorem code115_decoded :
    code { bytes := artifactBytes, pos := 25651, limit := 45644 } =
      .ok (Cache.raw.codes[115]!, { bytes := artifactBytes, pos := 25680, limit := 45644 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 25652, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 25655, limit := 25680 })
    (bodyFinish := { bytes := artifactBytes, pos := 25680, limit := 25680 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code115_seq_115_tail0_decoded
  · rfl

#print axioms code115_decoded

@[cbv_eval] theorem code116_seq_116_25_t_62_t_tail1_decoded :
    instructionSequenceAt 448 true { bytes := artifactBytes, pos := 25948, limit := 26225 } =
      .ok ((((((((Cache.raw.codes[116]!).body)[25]!).childBody false)[62]!).childBody false).drop 1, .otherwise), { bytes := artifactBytes, pos := 26077, limit := 26225 }) := by
  cbv

@[cbv_eval] theorem code116_seq_116_25_t_62_t_tail0_decoded :
    instructionSequenceAt 449 true { bytes := artifactBytes, pos := 25946, limit := 26225 } =
      .ok ((((((((Cache.raw.codes[116]!).body)[25]!).childBody false)[62]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 26077, limit := 26225 }) := by
  cbv

@[cbv_eval] theorem code116_seq_116_25_t_tail62_decoded :
    instructionSequenceAt 451 true { bytes := artifactBytes, pos := 25944, limit := 26225 } =
      .ok ((((((Cache.raw.codes[116]!).body)[25]!).childBody false).drop 62, .otherwise), { bytes := artifactBytes, pos := 26141, limit := 26225 }) := by
  cbv

@[cbv_eval] theorem code116_seq_116_25_t_tail2_decoded :
    instructionSequenceAt 511 true { bytes := artifactBytes, pos := 25816, limit := 26225 } =
      .ok ((((((Cache.raw.codes[116]!).body)[25]!).childBody false).drop 2, .otherwise), { bytes := artifactBytes, pos := 26141, limit := 26225 }) := by
  cbv

@[cbv_eval] theorem code116_seq_116_25_t_tail0_decoded :
    instructionSequenceAt 513 true { bytes := artifactBytes, pos := 25812, limit := 26225 } =
      .ok ((((((Cache.raw.codes[116]!).body)[25]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 26141, limit := 26225 }) := by
  cbv

@[cbv_eval] theorem code116_seq_116_tail25_decoded :
    instructionSequenceAt 515 false { bytes := artifactBytes, pos := 25810, limit := 26225 } =
      .ok ((((Cache.raw.codes[116]!).body).drop 25, .end), { bytes := artifactBytes, pos := 26225, limit := 26225 }) := by
  cbv

@[cbv_eval] theorem code116_seq_116_tail0_decoded :
    instructionSequenceAt 540 false { bytes := artifactBytes, pos := 25685, limit := 26225 } =
      .ok ((((Cache.raw.codes[116]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26225, limit := 26225 }) := by
  cbv

theorem code116_decoded :
    code { bytes := artifactBytes, pos := 25680, limit := 45644 } =
      .ok (Cache.raw.codes[116]!, { bytes := artifactBytes, pos := 26225, limit := 45644 }) := by
  refine code_eq_of_parts (size := 543)
    (payload := { bytes := artifactBytes, pos := 25682, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 25685, limit := 26225 })
    (bodyFinish := { bytes := artifactBytes, pos := 26225, limit := 26225 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code116_seq_116_tail0_decoded
  · rfl

#print axioms code116_decoded

@[cbv_eval] theorem code117_seq_117_29_t_69_t_tail45_decoded :
    instructionSequenceAt 516 true { bytes := artifactBytes, pos := 26645, limit := 26893 } =
      .ok ((((((((Cache.raw.codes[117]!).body)[29]!).childBody false)[69]!).childBody false).drop 45, .otherwise), { bytes := artifactBytes, pos := 26773, limit := 26893 }) := by
  cbv

@[cbv_eval] theorem code117_seq_117_29_t_69_t_tail0_decoded :
    instructionSequenceAt 561 true { bytes := artifactBytes, pos := 26521, limit := 26893 } =
      .ok ((((((((Cache.raw.codes[117]!).body)[29]!).childBody false)[69]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 26773, limit := 26893 }) := by
  cbv

@[cbv_eval] theorem code117_seq_117_29_t_tail69_decoded :
    instructionSequenceAt 563 true { bytes := artifactBytes, pos := 26519, limit := 26893 } =
      .ok ((((((Cache.raw.codes[117]!).body)[29]!).childBody false).drop 69, .otherwise), { bytes := artifactBytes, pos := 26825, limit := 26893 }) := by
  cbv

@[cbv_eval] theorem code117_seq_117_29_t_tail56_decoded :
    instructionSequenceAt 576 true { bytes := artifactBytes, pos := 26388, limit := 26893 } =
      .ok ((((((Cache.raw.codes[117]!).body)[29]!).childBody false).drop 56, .otherwise), { bytes := artifactBytes, pos := 26825, limit := 26893 }) := by
  cbv

@[cbv_eval] theorem code117_seq_117_29_t_tail0_decoded :
    instructionSequenceAt 632 true { bytes := artifactBytes, pos := 26298, limit := 26893 } =
      .ok ((((((Cache.raw.codes[117]!).body)[29]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 26825, limit := 26893 }) := by
  cbv

@[cbv_eval] theorem code117_seq_117_tail29_decoded :
    instructionSequenceAt 634 false { bytes := artifactBytes, pos := 26296, limit := 26893 } =
      .ok ((((Cache.raw.codes[117]!).body).drop 29, .end), { bytes := artifactBytes, pos := 26893, limit := 26893 }) := by
  cbv

end Project.EulerCertificate.Artifact
