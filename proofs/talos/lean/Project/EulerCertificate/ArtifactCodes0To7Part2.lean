import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes0To7Part1

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code3_seq_3_213_t_tail8_decoded :
    instructionSequenceAt 2561 true { bytes := artifactBytes, pos := 5029, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[213]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 5160, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_213_t_tail0_decoded :
    instructionSequenceAt 2569 true { bytes := artifactBytes, pos := 5016, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[213]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5160, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_328_t_tail0_decoded :
    instructionSequenceAt 2454 false { bytes := artifactBytes, pos := 5368, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[328]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5530, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_332_t_tail8_decoded :
    instructionSequenceAt 2442 true { bytes := artifactBytes, pos := 5550, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[332]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 5681, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_332_t_tail0_decoded :
    instructionSequenceAt 2450 true { bytes := artifactBytes, pos := 5537, limit := 5845 } =
      .ok ((((((Cache.raw.codes[3]!).body)[332]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5681, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail345_decoded :
    instructionSequenceAt 2439 false { bytes := artifactBytes, pos := 5704, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 345, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail332_decoded :
    instructionSequenceAt 2452 false { bytes := artifactBytes, pos := 5535, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 332, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail328_decoded :
    instructionSequenceAt 2456 false { bytes := artifactBytes, pos := 5366, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 328, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail258_decoded :
    instructionSequenceAt 2526 false { bytes := artifactBytes, pos := 5238, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 258, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail213_decoded :
    instructionSequenceAt 2571 false { bytes := artifactBytes, pos := 5014, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 213, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail209_decoded :
    instructionSequenceAt 2575 false { bytes := artifactBytes, pos := 4845, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 209, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail171_decoded :
    instructionSequenceAt 2613 false { bytes := artifactBytes, pos := 4716, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 171, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail156_decoded :
    instructionSequenceAt 2628 false { bytes := artifactBytes, pos := 4493, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 156, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail152_decoded :
    instructionSequenceAt 2632 false { bytes := artifactBytes, pos := 4324, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 152, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail99_decoded :
    instructionSequenceAt 2685 false { bytes := artifactBytes, pos := 4043, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 99, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail86_decoded :
    instructionSequenceAt 2698 false { bytes := artifactBytes, pos := 3874, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 86, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

end Project.EulerCertificate.Artifact
