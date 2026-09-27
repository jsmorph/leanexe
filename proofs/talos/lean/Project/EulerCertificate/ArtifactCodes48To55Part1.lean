import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes48To55Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_53_t_0_t_tail72_decoded :
    instructionSequenceAt 2381 false { bytes := artifactBytes, pos := 12713, limit := 14145 } =
      .ok ((((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[53]!).childBody false)[0]!).childBody false).drop 72, .end), { bytes := artifactBytes, pos := 12969, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_53_t_0_t_tail0_decoded :
    instructionSequenceAt 2453 false { bytes := artifactBytes, pos := 12593, limit := 14145 } =
      .ok ((((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[53]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12969, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_110_t_0_t_tail18_decoded :
    instructionSequenceAt 2378 false { bytes := artifactBytes, pos := 13112, limit := 14145 } =
      .ok ((((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[110]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 13240, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_110_t_0_t_tail0_decoded :
    instructionSequenceAt 2396 false { bytes := artifactBytes, pos := 13081, limit := 14145 } =
      .ok ((((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[110]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13240, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_t_52_t_tail0_decoded :
    instructionSequenceAt 2456 false { bytes := artifactBytes, pos := 11773, limit := 14145 } =
      .ok ((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false)[52]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11935, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_t_56_t_tail8_decoded :
    instructionSequenceAt 2444 true { bytes := artifactBytes, pos := 11955, limit := 14145 } =
      .ok ((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false)[56]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 12086, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_t_56_t_tail0_decoded :
    instructionSequenceAt 2452 true { bytes := artifactBytes, pos := 11942, limit := 14145 } =
      .ok ((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false)[56]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12086, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_36_t_tail0_decoded :
    instructionSequenceAt 2472 false { bytes := artifactBytes, pos := 12253, limit := 14145 } =
      .ok ((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[36]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12415, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_40_t_tail8_decoded :
    instructionSequenceAt 2460 true { bytes := artifactBytes, pos := 12435, limit := 14145 } =
      .ok ((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[40]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 12566, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_40_t_tail0_decoded :
    instructionSequenceAt 2468 true { bytes := artifactBytes, pos := 12422, limit := 14145 } =
      .ok ((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[40]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12566, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_53_t_tail0_decoded :
    instructionSequenceAt 2455 false { bytes := artifactBytes, pos := 12591, limit := 14145 } =
      .ok ((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[53]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12970, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_110_t_tail0_decoded :
    instructionSequenceAt 2398 false { bytes := artifactBytes, pos := 13079, limit := 14145 } =
      .ok ((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[110]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13241, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_114_t_tail8_decoded :
    instructionSequenceAt 2386 true { bytes := artifactBytes, pos := 13261, limit := 14145 } =
      .ok ((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[114]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 13392, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_114_t_tail0_decoded :
    instructionSequenceAt 2394 true { bytes := artifactBytes, pos := 13248, limit := 14145 } =
      .ok ((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[114]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13392, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_t_tail56_decoded :
    instructionSequenceAt 2454 true { bytes := artifactBytes, pos := 11940, limit := 14145 } =
      .ok ((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false).drop 56, .otherwise), { bytes := artifactBytes, pos := 12181, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_t_tail52_decoded :
    instructionSequenceAt 2458 true { bytes := artifactBytes, pos := 11771, limit := 14145 } =
      .ok ((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false).drop 52, .otherwise), { bytes := artifactBytes, pos := 12181, limit := 14145 }) := by
  cbv

end Project.EulerCertificate.Artifact
