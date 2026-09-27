import Project.EulerReconstructed.ArtifactCodes120To127Part2
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code125_seq_125_8_t_28_t_0_t_tail0_decoded :
    instructionSequenceAt 1321 false { bytes := artifactBytes, pos := 19296, limit := 19645 } =
      .ok ((((((((((Cache.raw.codes[125]!).body)[8]!).childBody false)[28]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19455, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_tail22_decoded :
    instructionSequenceAt 1333 false { bytes := artifactBytes, pos := 18347, limit := 19645 } =
      .ok ((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false).drop 22, .end), { bytes := artifactBytes, pos := 19230, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_0_t_tail0_decoded :
    instructionSequenceAt 1355 false { bytes := artifactBytes, pos := 18294, limit := 19645 } =
      .ok ((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19230, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_8_t_28_t_tail0_decoded :
    instructionSequenceAt 1323 false { bytes := artifactBytes, pos := 19294, limit := 19645 } =
      .ok ((((((((Cache.raw.codes[125]!).body)[8]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19456, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_8_t_32_t_tail8_decoded :
    instructionSequenceAt 1311 true { bytes := artifactBytes, pos := 19476, limit := 19645 } =
      .ok ((((((((Cache.raw.codes[125]!).body)[8]!).childBody false)[32]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 19607, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_8_t_32_t_tail0_decoded :
    instructionSequenceAt 1319 true { bytes := artifactBytes, pos := 19463, limit := 19645 } =
      .ok ((((((((Cache.raw.codes[125]!).body)[8]!).childBody false)[32]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19607, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_4_t_tail0_decoded :
    instructionSequenceAt 1357 false { bytes := artifactBytes, pos := 18292, limit := 19645 } =
      .ok ((((((Cache.raw.codes[125]!).body)[4]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19231, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_8_t_tail32_decoded :
    instructionSequenceAt 1321 true { bytes := artifactBytes, pos := 19461, limit := 19645 } =
      .ok ((((((Cache.raw.codes[125]!).body)[8]!).childBody false).drop 32, .otherwise), { bytes := artifactBytes, pos := 19635, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_8_t_tail28_decoded :
    instructionSequenceAt 1325 true { bytes := artifactBytes, pos := 19292, limit := 19645 } =
      .ok ((((((Cache.raw.codes[125]!).body)[8]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 19635, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_8_t_tail0_decoded :
    instructionSequenceAt 1353 true { bytes := artifactBytes, pos := 19238, limit := 19645 } =
      .ok ((((((Cache.raw.codes[125]!).body)[8]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 19635, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_tail8_decoded :
    instructionSequenceAt 1355 false { bytes := artifactBytes, pos := 19236, limit := 19645 } =
      .ok ((((Cache.raw.codes[125]!).body).drop 8, .end), { bytes := artifactBytes, pos := 19645, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_tail4_decoded :
    instructionSequenceAt 1359 false { bytes := artifactBytes, pos := 18290, limit := 19645 } =
      .ok ((((Cache.raw.codes[125]!).body).drop 4, .end), { bytes := artifactBytes, pos := 19645, limit := 19645 }) := by
  cbv

@[cbv_eval] theorem code125_seq_125_tail0_decoded :
    instructionSequenceAt 1363 false { bytes := artifactBytes, pos := 18282, limit := 19645 } =
      .ok ((((Cache.raw.codes[125]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19645, limit := 19645 }) := by
  cbv

theorem code125_decoded :
    code { bytes := artifactBytes, pos := 18277, limit := 30726 } =
      .ok (Cache.raw.codes[125]!, { bytes := artifactBytes, pos := 19645, limit := 30726 }) := by
  refine code_eq_of_parts (size := 1366)
    (payload := { bytes := artifactBytes, pos := 18279, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 18282, limit := 19645 })
    (bodyFinish := { bytes := artifactBytes, pos := 19645, limit := 19645 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code125_seq_125_tail0_decoded
  · rfl

#print axioms code125_decoded

@[cbv_eval] theorem code126_seq_126_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 19649, limit := 19656 } =
      .ok ((((Cache.raw.codes[126]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19656, limit := 19656 }) := by
  cbv

theorem code126_decoded :
    code { bytes := artifactBytes, pos := 19645, limit := 30726 } =
      .ok (Cache.raw.codes[126]!, { bytes := artifactBytes, pos := 19656, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 19646, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 19649, limit := 19656 })
    (bodyFinish := { bytes := artifactBytes, pos := 19656, limit := 19656 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code126_seq_126_tail0_decoded
  · rfl

#print axioms code126_decoded


end Project.EulerReconstructed.Artifact
