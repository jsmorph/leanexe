import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence5_9_t_tail11 :
    instructionSequenceAt 224 true { bytes := artifactBytes, pos := 1200, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[9]!) false).drop 11, .otherwise), { bytes := artifactBytes, pos := 1201, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_9_t_tail8 :
    instructionSequenceAt 227 true { bytes := artifactBytes, pos := 1195, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[9]!) false).drop 8, .otherwise), { bytes := artifactBytes, pos := 1201, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_9_t_tail0 :
    instructionSequenceAt 235 true { bytes := artifactBytes, pos := 1182, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[9]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1201, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_9_e_tail1 :
    instructionSequenceAt 234 false { bytes := artifactBytes, pos := 1202, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[9]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1203, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_9_e_tail0 :
    instructionSequenceAt 235 false { bytes := artifactBytes, pos := 1201, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[9]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1203, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_23_t_tail1 :
    instructionSequenceAt 220 true { bytes := artifactBytes, pos := 1230, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[23]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1231, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_23_t_tail0 :
    instructionSequenceAt 221 true { bytes := artifactBytes, pos := 1229, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[23]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1231, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_23_e_tail1 :
    instructionSequenceAt 220 false { bytes := artifactBytes, pos := 1233, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[23]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1234, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_23_e_tail0 :
    instructionSequenceAt 221 false { bytes := artifactBytes, pos := 1231, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[23]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1234, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_30_t_tail11 :
    instructionSequenceAt 203 true { bytes := artifactBytes, pos := 1265, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[30]!) false).drop 11, .otherwise), { bytes := artifactBytes, pos := 1266, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_30_t_tail8 :
    instructionSequenceAt 206 true { bytes := artifactBytes, pos := 1260, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[30]!) false).drop 8, .otherwise), { bytes := artifactBytes, pos := 1266, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_30_t_tail0 :
    instructionSequenceAt 214 true { bytes := artifactBytes, pos := 1247, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[30]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1266, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_30_e_tail1 :
    instructionSequenceAt 213 false { bytes := artifactBytes, pos := 1267, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[30]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1268, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_30_e_tail0 :
    instructionSequenceAt 214 false { bytes := artifactBytes, pos := 1266, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[30]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1268, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_44_t_tail1 :
    instructionSequenceAt 199 true { bytes := artifactBytes, pos := 1295, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[44]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1296, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_44_t_tail0 :
    instructionSequenceAt 200 true { bytes := artifactBytes, pos := 1294, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[44]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1296, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_44_e_tail1 :
    instructionSequenceAt 199 false { bytes := artifactBytes, pos := 1298, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[44]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1299, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_44_e_tail0 :
    instructionSequenceAt 200 false { bytes := artifactBytes, pos := 1296, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[44]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1299, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_51_t_tail11 :
    instructionSequenceAt 182 true { bytes := artifactBytes, pos := 1330, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[51]!) false).drop 11, .otherwise), { bytes := artifactBytes, pos := 1331, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_51_t_tail8 :
    instructionSequenceAt 185 true { bytes := artifactBytes, pos := 1325, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[51]!) false).drop 8, .otherwise), { bytes := artifactBytes, pos := 1331, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_51_t_tail0 :
    instructionSequenceAt 193 true { bytes := artifactBytes, pos := 1312, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[51]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1331, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_51_e_tail1 :
    instructionSequenceAt 192 false { bytes := artifactBytes, pos := 1332, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[51]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1333, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_51_e_tail0 :
    instructionSequenceAt 193 false { bytes := artifactBytes, pos := 1331, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[51]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1333, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_65_t_tail1 :
    instructionSequenceAt 178 true { bytes := artifactBytes, pos := 1360, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[65]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1361, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_65_t_tail0 :
    instructionSequenceAt 179 true { bytes := artifactBytes, pos := 1359, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[65]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1361, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_65_e_tail1 :
    instructionSequenceAt 178 false { bytes := artifactBytes, pos := 1363, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[65]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1364, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_65_e_tail0 :
    instructionSequenceAt 179 false { bytes := artifactBytes, pos := 1361, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[65]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1364, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_72_t_tail11 :
    instructionSequenceAt 161 true { bytes := artifactBytes, pos := 1395, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[72]!) false).drop 11, .otherwise), { bytes := artifactBytes, pos := 1396, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_72_t_tail8 :
    instructionSequenceAt 164 true { bytes := artifactBytes, pos := 1390, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[72]!) false).drop 8, .otherwise), { bytes := artifactBytes, pos := 1396, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_72_t_tail0 :
    instructionSequenceAt 172 true { bytes := artifactBytes, pos := 1377, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[72]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1396, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_72_e_tail1 :
    instructionSequenceAt 171 false { bytes := artifactBytes, pos := 1397, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[72]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1398, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_72_e_tail0 :
    instructionSequenceAt 172 false { bytes := artifactBytes, pos := 1396, limit := 1409 } =
      .ok (((Instr.childBody ((Cache.raw.codes[5]!.body)[72]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1398, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_tail78 :
    instructionSequenceAt 168 false { bytes := artifactBytes, pos := 1408, limit := 1409 } =
      .ok (((Cache.raw.codes[5]!.body).drop 78, .end), { bytes := artifactBytes, pos := 1409, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_tail72 :
    instructionSequenceAt 174 false { bytes := artifactBytes, pos := 1375, limit := 1409 } =
      .ok (((Cache.raw.codes[5]!.body).drop 72, .end), { bytes := artifactBytes, pos := 1409, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_tail64 :
    instructionSequenceAt 182 false { bytes := artifactBytes, pos := 1356, limit := 1409 } =
      .ok (((Cache.raw.codes[5]!.body).drop 64, .end), { bytes := artifactBytes, pos := 1409, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_tail56 :
    instructionSequenceAt 190 false { bytes := artifactBytes, pos := 1341, limit := 1409 } =
      .ok (((Cache.raw.codes[5]!.body).drop 56, .end), { bytes := artifactBytes, pos := 1409, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_tail48 :
    instructionSequenceAt 198 false { bytes := artifactBytes, pos := 1305, limit := 1409 } =
      .ok (((Cache.raw.codes[5]!.body).drop 48, .end), { bytes := artifactBytes, pos := 1409, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_tail40 :
    instructionSequenceAt 206 false { bytes := artifactBytes, pos := 1286, limit := 1409 } =
      .ok (((Cache.raw.codes[5]!.body).drop 40, .end), { bytes := artifactBytes, pos := 1409, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_tail32 :
    instructionSequenceAt 214 false { bytes := artifactBytes, pos := 1270, limit := 1409 } =
      .ok (((Cache.raw.codes[5]!.body).drop 32, .end), { bytes := artifactBytes, pos := 1409, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_tail24 :
    instructionSequenceAt 222 false { bytes := artifactBytes, pos := 1234, limit := 1409 } =
      .ok (((Cache.raw.codes[5]!.body).drop 24, .end), { bytes := artifactBytes, pos := 1409, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_tail16 :
    instructionSequenceAt 230 false { bytes := artifactBytes, pos := 1215, limit := 1409 } =
      .ok (((Cache.raw.codes[5]!.body).drop 16, .end), { bytes := artifactBytes, pos := 1409, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_tail8 :
    instructionSequenceAt 238 false { bytes := artifactBytes, pos := 1179, limit := 1409 } =
      .ok (((Cache.raw.codes[5]!.body).drop 8, .end), { bytes := artifactBytes, pos := 1409, limit := 1409 }) := by cbv

@[cbv_eval] theorem sequence5_tail0 :
    instructionSequenceAt 246 false { bytes := artifactBytes, pos := 1163, limit := 1409 } =
      .ok (((Cache.raw.codes[5]!.body).drop 0, .end), { bytes := artifactBytes, pos := 1409, limit := 1409 }) := by cbv

theorem code5_decoded_parts :
    code { bytes := artifactBytes, pos := 1158, limit := 16006 } = .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 1409, limit := 16006 }) := by
  refine code_eq_of_parts (size := 249)
    (payload := { bytes := artifactBytes, pos := 1160, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 1163, limit := 1409 })
    (bodyFinish := { bytes := artifactBytes, pos := 1409, limit := 1409 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence5_tail0
  · rfl

#print axioms code5_decoded_parts
end Project.TinyGpt2Hidden.Artifact
