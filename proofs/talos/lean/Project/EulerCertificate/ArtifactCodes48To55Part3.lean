import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes48To55Part2

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code52_seq_52_8_t_tail56_decoded :
    instructionSequenceAt 2468 true { bytes := artifactBytes, pos := 13902, limit := 14145 } =
      .ok ((((((Cache.raw.codes[52]!).body)[8]!).childBody false).drop 56, .otherwise), { bytes := artifactBytes, pos := 14139, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_8_t_tail52_decoded :
    instructionSequenceAt 2472 true { bytes := artifactBytes, pos := 13733, limit := 14145 } =
      .ok ((((((Cache.raw.codes[52]!).body)[8]!).childBody false).drop 52, .otherwise), { bytes := artifactBytes, pos := 14139, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_8_t_tail0_decoded :
    instructionSequenceAt 2524 true { bytes := artifactBytes, pos := 13620, limit := 14145 } =
      .ok ((((((Cache.raw.codes[52]!).body)[8]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 14139, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_tail8_decoded :
    instructionSequenceAt 2526 false { bytes := artifactBytes, pos := 13618, limit := 14145 } =
      .ok ((((Cache.raw.codes[52]!).body).drop 8, .end), { bytes := artifactBytes, pos := 14145, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_tail4_decoded :
    instructionSequenceAt 2530 false { bytes := artifactBytes, pos := 11619, limit := 14145 } =
      .ok ((((Cache.raw.codes[52]!).body).drop 4, .end), { bytes := artifactBytes, pos := 14145, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_tail0_decoded :
    instructionSequenceAt 2534 false { bytes := artifactBytes, pos := 11611, limit := 14145 } =
      .ok ((((Cache.raw.codes[52]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14145, limit := 14145 }) := by
  cbv

theorem code52_decoded :
    code { bytes := artifactBytes, pos := 11606, limit := 45644 } =
      .ok (Cache.raw.codes[52]!, { bytes := artifactBytes, pos := 14145, limit := 45644 }) := by
  refine code_eq_of_parts (size := 2537)
    (payload := { bytes := artifactBytes, pos := 11608, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 11611, limit := 14145 })
    (bodyFinish := { bytes := artifactBytes, pos := 14145, limit := 14145 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code52_seq_52_tail0_decoded
  · rfl

#print axioms code52_decoded

@[cbv_eval] theorem code53_seq_53_4_t_51_t_0_t_tail18_decoded :
    instructionSequenceAt 1003 false { bytes := artifactBytes, pos := 14325, limit := 15232 } =
      .ok ((((((((((Cache.raw.codes[53]!).body)[4]!).childBody false)[51]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 14453, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_t_51_t_0_t_tail0_decoded :
    instructionSequenceAt 1021 false { bytes := artifactBytes, pos := 14294, limit := 15232 } =
      .ok ((((((((((Cache.raw.codes[53]!).body)[4]!).childBody false)[51]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14453, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_e_24_t_0_t_tail18_decoded :
    instructionSequenceAt 1030 false { bytes := artifactBytes, pos := 14915, limit := 15232 } =
      .ok ((((((((((Cache.raw.codes[53]!).body)[4]!).childBody true)[24]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 15043, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_e_24_t_0_t_tail0_decoded :
    instructionSequenceAt 1048 false { bytes := artifactBytes, pos := 14884, limit := 15232 } =
      .ok ((((((((((Cache.raw.codes[53]!).body)[4]!).childBody true)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15043, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_t_51_t_tail0_decoded :
    instructionSequenceAt 1023 false { bytes := artifactBytes, pos := 14292, limit := 15232 } =
      .ok ((((((((Cache.raw.codes[53]!).body)[4]!).childBody false)[51]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14454, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_t_55_t_tail8_decoded :
    instructionSequenceAt 1011 true { bytes := artifactBytes, pos := 14474, limit := 15232 } =
      .ok ((((((((Cache.raw.codes[53]!).body)[4]!).childBody false)[55]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 14605, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_t_55_t_tail0_decoded :
    instructionSequenceAt 1019 true { bytes := artifactBytes, pos := 14461, limit := 15232 } =
      .ok ((((((((Cache.raw.codes[53]!).body)[4]!).childBody false)[55]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14605, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_e_24_t_tail0_decoded :
    instructionSequenceAt 1050 false { bytes := artifactBytes, pos := 14882, limit := 15232 } =
      .ok ((((((((Cache.raw.codes[53]!).body)[4]!).childBody true)[24]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15044, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_e_28_t_tail8_decoded :
    instructionSequenceAt 1038 true { bytes := artifactBytes, pos := 15064, limit := 15232 } =
      .ok ((((((((Cache.raw.codes[53]!).body)[4]!).childBody true)[28]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 15195, limit := 15232 }) := by
  cbv

end Project.EulerCertificate.Artifact
