import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes0To7Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code3_seq_3_209_t_0_t_tail18_decoded :
    instructionSequenceAt 2553 false { bytes := artifactBytes, pos := 4880, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[209]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 5008, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_209_t_0_t_tail0_decoded :
    instructionSequenceAt 2571 false { bytes := artifactBytes, pos := 4849, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[209]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5008, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_328_t_0_t_tail18_decoded :
    instructionSequenceAt 2434 false { bytes := artifactBytes, pos := 5401, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[328]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 5529, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_328_t_0_t_tail0_decoded :
    instructionSequenceAt 2452 false { bytes := artifactBytes, pos := 5370, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[328]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5529, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_30_t_tail0_decoded :
    instructionSequenceAt 2752 false { bytes := artifactBytes, pos := 3121, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[30]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3283, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_34_t_tail8_decoded :
    instructionSequenceAt 2740 true { bytes := artifactBytes, pos := 3303, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[34]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 3434, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_34_t_tail0_decoded :
    instructionSequenceAt 2748 true { bytes := artifactBytes, pos := 3290, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[34]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3434, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_47_t_tail0_decoded :
    instructionSequenceAt 2735 false { bytes := artifactBytes, pos := 3459, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[47]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3639, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_82_t_tail0_decoded :
    instructionSequenceAt 2700 false { bytes := artifactBytes, pos := 3707, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[82]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3869, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_86_t_tail8_decoded :
    instructionSequenceAt 2688 true { bytes := artifactBytes, pos := 3889, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[86]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 4020, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_86_t_tail0_decoded :
    instructionSequenceAt 2696 true { bytes := artifactBytes, pos := 3876, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[86]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4020, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_99_t_tail0_decoded :
    instructionSequenceAt 2683 false { bytes := artifactBytes, pos := 4045, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[99]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4225, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_152_t_tail0_decoded :
    instructionSequenceAt 2630 false { bytes := artifactBytes, pos := 4326, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[152]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4488, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_156_t_tail8_decoded :
    instructionSequenceAt 2618 true { bytes := artifactBytes, pos := 4508, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[156]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 4639, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_156_t_tail0_decoded :
    instructionSequenceAt 2626 true { bytes := artifactBytes, pos := 4495, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[156]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4639, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_209_t_tail0_decoded :
    instructionSequenceAt 2573 false { bytes := artifactBytes, pos := 4847, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[209]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5009, limit := 5845 }) := by
  cbv

end Project.EulerCertificate.Artifact
