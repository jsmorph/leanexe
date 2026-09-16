import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes48To55Part1

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_t_tail0_decoded :
    instructionSequenceAt 2510 true { bytes := artifactBytes, pos := 11658, limit := 14145 } =
      .ok ((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 12181, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_tail130_decoded :
    instructionSequenceAt 2380 false { bytes := artifactBytes, pos := 13471, limit := 14145 } =
      .ok ((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 130, .end), { bytes := artifactBytes, pos := 13609, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_tail114_decoded :
    instructionSequenceAt 2396 false { bytes := artifactBytes, pos := 13246, limit := 14145 } =
      .ok ((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 114, .end), { bytes := artifactBytes, pos := 13609, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_tail110_decoded :
    instructionSequenceAt 2400 false { bytes := artifactBytes, pos := 13077, limit := 14145 } =
      .ok ((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 110, .end), { bytes := artifactBytes, pos := 13609, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_tail53_decoded :
    instructionSequenceAt 2457 false { bytes := artifactBytes, pos := 12589, limit := 14145 } =
      .ok ((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 53, .end), { bytes := artifactBytes, pos := 13609, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_tail40_decoded :
    instructionSequenceAt 2470 false { bytes := artifactBytes, pos := 12420, limit := 14145 } =
      .ok ((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 40, .end), { bytes := artifactBytes, pos := 13609, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_tail36_decoded :
    instructionSequenceAt 2474 false { bytes := artifactBytes, pos := 12251, limit := 14145 } =
      .ok ((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 36, .end), { bytes := artifactBytes, pos := 13609, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_tail0_decoded :
    instructionSequenceAt 2510 false { bytes := artifactBytes, pos := 12181, limit := 14145 } =
      .ok ((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 13609, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_8_t_52_t_0_t_tail18_decoded :
    instructionSequenceAt 2450 false { bytes := artifactBytes, pos := 13768, limit := 14145 } =
      .ok ((((((((((Cache.raw.codes[52]!).body)[8]!).childBody false)[52]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 13896, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_8_t_52_t_0_t_tail0_decoded :
    instructionSequenceAt 2468 false { bytes := artifactBytes, pos := 13737, limit := 14145 } =
      .ok ((((((((((Cache.raw.codes[52]!).body)[8]!).childBody false)[52]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13896, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_tail14_decoded :
    instructionSequenceAt 2512 false { bytes := artifactBytes, pos := 11656, limit := 14145 } =
      .ok ((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 13612, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_tail0_decoded :
    instructionSequenceAt 2526 false { bytes := artifactBytes, pos := 11623, limit := 14145 } =
      .ok ((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13612, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_8_t_52_t_tail0_decoded :
    instructionSequenceAt 2470 false { bytes := artifactBytes, pos := 13735, limit := 14145 } =
      .ok ((((((((Cache.raw.codes[52]!).body)[8]!).childBody false)[52]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13897, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_8_t_56_t_tail8_decoded :
    instructionSequenceAt 2458 true { bytes := artifactBytes, pos := 13917, limit := 14145 } =
      .ok ((((((((Cache.raw.codes[52]!).body)[8]!).childBody false)[56]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 14048, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_8_t_56_t_tail0_decoded :
    instructionSequenceAt 2466 true { bytes := artifactBytes, pos := 13904, limit := 14145 } =
      .ok ((((((((Cache.raw.codes[52]!).body)[8]!).childBody false)[56]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14048, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_tail0_decoded :
    instructionSequenceAt 2528 false { bytes := artifactBytes, pos := 11621, limit := 14145 } =
      .ok ((((((Cache.raw.codes[52]!).body)[4]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13613, limit := 14145 }) := by
  cbv

end Project.EulerCertificate.Artifact
