import Project.EulerReconstructed.ArtifactCodes120To127Part1
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_t_26_t_37_e_tail0_decoded :
    instructionSequenceAt 1264 false { bytes := artifactBytes, pos := 18511, limit := 19645 } =
      .ok ((((((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false)[26]!).childBody false)[37]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 18672, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_e_28_t_0_t_tail18_decoded :
    instructionSequenceAt 1281 false { bytes := artifactBytes, pos := 18915, limit := 19645 } =
      .ok ((((((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 19043, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_e_28_t_0_t_tail0_decoded :
    instructionSequenceAt 1299 false { bytes := artifactBytes, pos := 18884, limit := 19645 } =
      .ok ((((((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19043, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_t_26_t_tail37_decoded :
    instructionSequenceAt 1266 true { bytes := artifactBytes, pos := 18488, limit := 19645 } =
      .ok ((((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false)[26]!).childBody false).drop 37, .otherwise), { bytes := artifactBytes, pos := 18673, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_t_26_t_tail0_decoded :
    instructionSequenceAt 1303 true { bytes := artifactBytes, pos := 18411, limit := 19645 } =
      .ok ((((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false)[26]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 18673, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_t_26_e_tail8_decoded :
    instructionSequenceAt 1295 false { bytes := artifactBytes, pos := 18696, limit := 19645 } =
      .ok ((((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false)[26]!).childBody true).drop 8, .end), { bytes := artifactBytes, pos := 18825, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_t_26_e_tail0_decoded :
    instructionSequenceAt 1303 false { bytes := artifactBytes, pos := 18673, limit := 19645 } =
      .ok ((((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false)[26]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 18825, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_e_28_t_tail0_decoded :
    instructionSequenceAt 1301 false { bytes := artifactBytes, pos := 18882, limit := 19645 } =
      .ok ((((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19044, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_e_32_t_tail8_decoded :
    instructionSequenceAt 1289 true { bytes := artifactBytes, pos := 19064, limit := 19645 } =
      .ok ((((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true)[32]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 19195, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_e_32_t_tail0_decoded :
    instructionSequenceAt 1297 true { bytes := artifactBytes, pos := 19051, limit := 19645 } =
      .ok ((((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true)[32]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19195, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_t_tail26_decoded :
    instructionSequenceAt 1305 true { bytes := artifactBytes, pos := 18409, limit := 19645 } =
      .ok ((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 18826, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_t_tail0_decoded :
    instructionSequenceAt 1331 true { bytes := artifactBytes, pos := 18349, limit := 19645 } =
      .ok ((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 18826, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_e_tail32_decoded :
    instructionSequenceAt 1299 false { bytes := artifactBytes, pos := 19049, limit := 19645 } =
      .ok ((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true).drop 32, .end), { bytes := artifactBytes, pos := 19227, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_e_tail28_decoded :
    instructionSequenceAt 1303 false { bytes := artifactBytes, pos := 18880, limit := 19645 } =
      .ok ((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true).drop 28, .end), { bytes := artifactBytes, pos := 19227, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_e_tail0_decoded :
    instructionSequenceAt 1331 false { bytes := artifactBytes, pos := 18826, limit := 19645 } =
      .ok ((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 19227, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_8_t_28_t_0_t_tail18_decoded :
    instructionSequenceAt 1303 false { bytes := artifactBytes, pos := 19327, limit := 19645 } =
      .ok ((((((((((Cache.raw.codes[125]!).body)[8]!).childBody false)[28]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 19455, limit := 19645 }) := by
  cbv


end Project.EulerReconstructed.Artifact
