import Project.EulerReconstructed.ArtifactCodes136To143Part2
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_tail53_decoded :
    instructionSequenceAt 2458 false { bytes := artifactBytes, pos := 23793, limit := 25350 } =
      .ok ((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 53, .end), { bytes := artifactBytes, pos := 24814, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_tail40_decoded :
    instructionSequenceAt 2471 false { bytes := artifactBytes, pos := 23624, limit := 25350 } =
      .ok ((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 40, .end), { bytes := artifactBytes, pos := 24814, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_tail36_decoded :
    instructionSequenceAt 2475 false { bytes := artifactBytes, pos := 23455, limit := 25350 } =
      .ok ((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 36, .end), { bytes := artifactBytes, pos := 24814, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_tail0_decoded :
    instructionSequenceAt 2511 false { bytes := artifactBytes, pos := 23385, limit := 25350 } =
      .ok ((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 24814, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_8_t_52_t_0_t_tail18_decoded :
    instructionSequenceAt 2451 false { bytes := artifactBytes, pos := 24973, limit := 25350 } =
      .ok ((((((((((Cache.raw.codes[140]!).body)[8]!).childBody false)[52]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 25101, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_8_t_52_t_0_t_tail0_decoded :
    instructionSequenceAt 2469 false { bytes := artifactBytes, pos := 24942, limit := 25350 } =
      .ok ((((((((((Cache.raw.codes[140]!).body)[8]!).childBody false)[52]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25101, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_tail14_decoded :
    instructionSequenceAt 2513 false { bytes := artifactBytes, pos := 22860, limit := 25350 } =
      .ok ((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 24817, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_tail0_decoded :
    instructionSequenceAt 2527 false { bytes := artifactBytes, pos := 22827, limit := 25350 } =
      .ok ((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24817, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_8_t_52_t_tail0_decoded :
    instructionSequenceAt 2471 false { bytes := artifactBytes, pos := 24940, limit := 25350 } =
      .ok ((((((((Cache.raw.codes[140]!).body)[8]!).childBody false)[52]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25102, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_8_t_56_t_tail8_decoded :
    instructionSequenceAt 2459 true { bytes := artifactBytes, pos := 25122, limit := 25350 } =
      .ok ((((((((Cache.raw.codes[140]!).body)[8]!).childBody false)[56]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 25253, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_8_t_56_t_tail0_decoded :
    instructionSequenceAt 2467 true { bytes := artifactBytes, pos := 25109, limit := 25350 } =
      .ok ((((((((Cache.raw.codes[140]!).body)[8]!).childBody false)[56]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25253, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_tail0_decoded :
    instructionSequenceAt 2529 false { bytes := artifactBytes, pos := 22825, limit := 25350 } =
      .ok ((((((Cache.raw.codes[140]!).body)[4]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24818, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_8_t_tail56_decoded :
    instructionSequenceAt 2469 true { bytes := artifactBytes, pos := 25107, limit := 25350 } =
      .ok ((((((Cache.raw.codes[140]!).body)[8]!).childBody false).drop 56, .otherwise), { bytes := artifactBytes, pos := 25344, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_8_t_tail52_decoded :
    instructionSequenceAt 2473 true { bytes := artifactBytes, pos := 24938, limit := 25350 } =
      .ok ((((((Cache.raw.codes[140]!).body)[8]!).childBody false).drop 52, .otherwise), { bytes := artifactBytes, pos := 25344, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_8_t_tail0_decoded :
    instructionSequenceAt 2525 true { bytes := artifactBytes, pos := 24825, limit := 25350 } =
      .ok ((((((Cache.raw.codes[140]!).body)[8]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 25344, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_tail8_decoded :
    instructionSequenceAt 2527 false { bytes := artifactBytes, pos := 24823, limit := 25350 } =
      .ok ((((Cache.raw.codes[140]!).body).drop 8, .end), { bytes := artifactBytes, pos := 25350, limit := 25350 }) := by
  cbv


end Project.EulerReconstructed.Artifact
