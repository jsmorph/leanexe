import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes8To15Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code15_seq_15_305_t_0_t_tail18_decoded :
    instructionSequenceAt 1020 false { bytes := artifactBytes, pos := 6985, limit := 7438 } =
      .ok ((((((((Cache.raw.codes[15]!).body)[305]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 7113, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_305_t_0_t_tail0_decoded :
    instructionSequenceAt 1038 false { bytes := artifactBytes, pos := 6954, limit := 7438 } =
      .ok ((((((((Cache.raw.codes[15]!).body)[305]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7113, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_70_t_tail0_decoded :
    instructionSequenceAt 1275 false { bytes := artifactBytes, pos := 6231, limit := 7438 } =
      .ok ((((((Cache.raw.codes[15]!).body)[70]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6393, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_74_t_tail8_decoded :
    instructionSequenceAt 1263 true { bytes := artifactBytes, pos := 6413, limit := 7438 } =
      .ok ((((((Cache.raw.codes[15]!).body)[74]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 6544, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_74_t_tail0_decoded :
    instructionSequenceAt 1271 true { bytes := artifactBytes, pos := 6400, limit := 7438 } =
      .ok ((((((Cache.raw.codes[15]!).body)[74]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6544, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_305_t_tail0_decoded :
    instructionSequenceAt 1040 false { bytes := artifactBytes, pos := 6952, limit := 7438 } =
      .ok ((((((Cache.raw.codes[15]!).body)[305]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7114, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_309_t_tail8_decoded :
    instructionSequenceAt 1028 true { bytes := artifactBytes, pos := 7134, limit := 7438 } =
      .ok ((((((Cache.raw.codes[15]!).body)[309]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 7265, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_309_t_tail0_decoded :
    instructionSequenceAt 1036 true { bytes := artifactBytes, pos := 7121, limit := 7438 } =
      .ok ((((((Cache.raw.codes[15]!).body)[309]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7265, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_tail322_decoded :
    instructionSequenceAt 1025 false { bytes := artifactBytes, pos := 7288, limit := 7438 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 322, .end), { bytes := artifactBytes, pos := 7438, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_tail309_decoded :
    instructionSequenceAt 1038 false { bytes := artifactBytes, pos := 7119, limit := 7438 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 309, .end), { bytes := artifactBytes, pos := 7438, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_tail305_decoded :
    instructionSequenceAt 1042 false { bytes := artifactBytes, pos := 6950, limit := 7438 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 305, .end), { bytes := artifactBytes, pos := 7438, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_tail237_decoded :
    instructionSequenceAt 1110 false { bytes := artifactBytes, pos := 6822, limit := 7438 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 237, .end), { bytes := artifactBytes, pos := 7438, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_tail161_decoded :
    instructionSequenceAt 1186 false { bytes := artifactBytes, pos := 6694, limit := 7438 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 161, .end), { bytes := artifactBytes, pos := 7438, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_tail86_decoded :
    instructionSequenceAt 1261 false { bytes := artifactBytes, pos := 6565, limit := 7438 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 86, .end), { bytes := artifactBytes, pos := 7438, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_tail74_decoded :
    instructionSequenceAt 1273 false { bytes := artifactBytes, pos := 6398, limit := 7438 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 74, .end), { bytes := artifactBytes, pos := 7438, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_tail70_decoded :
    instructionSequenceAt 1277 false { bytes := artifactBytes, pos := 6229, limit := 7438 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 70, .end), { bytes := artifactBytes, pos := 7438, limit := 7438 }) := by
  cbv

end Project.EulerCertificate.Artifact
