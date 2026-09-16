import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes176To183Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_t_26_t_tail0_decoded :
    instructionSequenceAt 1535 true { bytes := artifactBytes, pos := 39873, limit := 41339 } =
      .ok ((((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false)[26]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 40171, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_t_26_e_tail8_decoded :
    instructionSequenceAt 1527 false { bytes := artifactBytes, pos := 40194, limit := 41339 } =
      .ok ((((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false)[26]!).childBody true).drop 8, .end), { bytes := artifactBytes, pos := 40323, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_t_26_e_tail0_decoded :
    instructionSequenceAt 1535 false { bytes := artifactBytes, pos := 40171, limit := 41339 } =
      .ok ((((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false)[26]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 40323, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_e_28_t_tail0_decoded :
    instructionSequenceAt 1533 false { bytes := artifactBytes, pos := 40381, limit := 41339 } =
      .ok ((((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 40545, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_e_32_t_tail12_decoded :
    instructionSequenceAt 1517 true { bytes := artifactBytes, pos := 40575, limit := 41339 } =
      .ok ((((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true)[32]!).childBody false).drop 12, .end), { bytes := artifactBytes, pos := 40704, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_e_32_t_tail0_decoded :
    instructionSequenceAt 1529 true { bytes := artifactBytes, pos := 40553, limit := 41339 } =
      .ok ((((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true)[32]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 40704, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_t_tail26_decoded :
    instructionSequenceAt 1537 true { bytes := artifactBytes, pos := 39871, limit := 41339 } =
      .ok ((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 40324, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_t_tail0_decoded :
    instructionSequenceAt 1563 true { bytes := artifactBytes, pos := 39811, limit := 41339 } =
      .ok ((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 40324, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_e_tail32_decoded :
    instructionSequenceAt 1531 false { bytes := artifactBytes, pos := 40551, limit := 41339 } =
      .ok ((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true).drop 32, .end), { bytes := artifactBytes, pos := 40811, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_e_tail28_decoded :
    instructionSequenceAt 1535 false { bytes := artifactBytes, pos := 40379, limit := 41339 } =
      .ok ((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true).drop 28, .end), { bytes := artifactBytes, pos := 40811, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_e_tail0_decoded :
    instructionSequenceAt 1563 false { bytes := artifactBytes, pos := 40324, limit := 41339 } =
      .ok ((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 40811, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_8_t_28_t_0_t_tail18_decoded :
    instructionSequenceAt 1535 false { bytes := artifactBytes, pos := 40913, limit := 41339 } =
      .ok ((((((((((Cache.raw.codes[179]!).body)[8]!).childBody false)[28]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 41042, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_8_t_28_t_0_t_tail0_decoded :
    instructionSequenceAt 1553 false { bytes := artifactBytes, pos := 40881, limit := 41339 } =
      .ok ((((((((((Cache.raw.codes[179]!).body)[8]!).childBody false)[28]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 41042, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_tail22_decoded :
    instructionSequenceAt 1565 false { bytes := artifactBytes, pos := 39809, limit := 41339 } =
      .ok ((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false).drop 22, .end), { bytes := artifactBytes, pos := 40814, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_tail0_decoded :
    instructionSequenceAt 1587 false { bytes := artifactBytes, pos := 39756, limit := 41339 } =
      .ok ((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 40814, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_8_t_28_t_tail0_decoded :
    instructionSequenceAt 1555 false { bytes := artifactBytes, pos := 40879, limit := 41339 } =
      .ok ((((((((Cache.raw.codes[179]!).body)[8]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 41043, limit := 41339 }) := by
  cbv

end Project.EulerCertificate.Artifact
