import Project.EulerReconstructed.ArtifactCodes136To143Part1
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_t_52_t_tail0_decoded :
    instructionSequenceAt 2457 false { bytes := artifactBytes, pos := 22977, limit := 25350 } =
      .ok ((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false)[52]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23139, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_t_56_t_tail8_decoded :
    instructionSequenceAt 2445 true { bytes := artifactBytes, pos := 23159, limit := 25350 } =
      .ok ((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false)[56]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 23290, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_t_56_t_tail0_decoded :
    instructionSequenceAt 2453 true { bytes := artifactBytes, pos := 23146, limit := 25350 } =
      .ok ((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false)[56]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23290, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_36_t_tail0_decoded :
    instructionSequenceAt 2473 false { bytes := artifactBytes, pos := 23457, limit := 25350 } =
      .ok ((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[36]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23619, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_40_t_tail8_decoded :
    instructionSequenceAt 2461 true { bytes := artifactBytes, pos := 23639, limit := 25350 } =
      .ok ((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[40]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 23770, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_40_t_tail0_decoded :
    instructionSequenceAt 2469 true { bytes := artifactBytes, pos := 23626, limit := 25350 } =
      .ok ((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[40]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23770, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_53_t_tail0_decoded :
    instructionSequenceAt 2456 false { bytes := artifactBytes, pos := 23795, limit := 25350 } =
      .ok ((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[53]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24175, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_110_t_tail0_decoded :
    instructionSequenceAt 2399 false { bytes := artifactBytes, pos := 24284, limit := 25350 } =
      .ok ((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[110]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24446, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_114_t_tail8_decoded :
    instructionSequenceAt 2387 true { bytes := artifactBytes, pos := 24466, limit := 25350 } =
      .ok ((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[114]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 24597, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_114_t_tail0_decoded :
    instructionSequenceAt 2395 true { bytes := artifactBytes, pos := 24453, limit := 25350 } =
      .ok ((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[114]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24597, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_t_tail56_decoded :
    instructionSequenceAt 2455 true { bytes := artifactBytes, pos := 23144, limit := 25350 } =
      .ok ((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false).drop 56, .otherwise), { bytes := artifactBytes, pos := 23385, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_t_tail52_decoded :
    instructionSequenceAt 2459 true { bytes := artifactBytes, pos := 22975, limit := 25350 } =
      .ok ((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false).drop 52, .otherwise), { bytes := artifactBytes, pos := 23385, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_t_tail0_decoded :
    instructionSequenceAt 2511 true { bytes := artifactBytes, pos := 22862, limit := 25350 } =
      .ok ((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 23385, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_tail130_decoded :
    instructionSequenceAt 2381 false { bytes := artifactBytes, pos := 24676, limit := 25350 } =
      .ok ((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 130, .end), { bytes := artifactBytes, pos := 24814, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_tail114_decoded :
    instructionSequenceAt 2397 false { bytes := artifactBytes, pos := 24451, limit := 25350 } =
      .ok ((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 114, .end), { bytes := artifactBytes, pos := 24814, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_tail110_decoded :
    instructionSequenceAt 2401 false { bytes := artifactBytes, pos := 24282, limit := 25350 } =
      .ok ((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 110, .end), { bytes := artifactBytes, pos := 24814, limit := 25350 }) := by
  cbv


end Project.EulerReconstructed.Artifact
