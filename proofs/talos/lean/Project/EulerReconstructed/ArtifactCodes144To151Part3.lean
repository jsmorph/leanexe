import Project.EulerReconstructed.ArtifactCodes144To151Part2
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code145_seq_145_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 29773, limit := 29780 } =
      .ok ((((Cache.raw.codes[145]!).body).drop 0, .end), { bytes := artifactBytes, pos := 29780, limit := 29780 }) := by
  cbv

theorem code145_decoded :
    code { bytes := artifactBytes, pos := 29769, limit := 30726 } =
      .ok (Cache.raw.codes[145]!, { bytes := artifactBytes, pos := 29780, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 29770, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 29773, limit := 29780 })
    (bodyFinish := { bytes := artifactBytes, pos := 29780, limit := 29780 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code145_seq_145_tail0_decoded
  · rfl

#print axioms code145_decoded

@[cbv_eval] theorem code146_seq_146_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 29784, limit := 29791 } =
      .ok ((((Cache.raw.codes[146]!).body).drop 0, .end), { bytes := artifactBytes, pos := 29791, limit := 29791 }) := by
  cbv

theorem code146_decoded :
    code { bytes := artifactBytes, pos := 29780, limit := 30726 } =
      .ok (Cache.raw.codes[146]!, { bytes := artifactBytes, pos := 29791, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 29781, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 29784, limit := 29791 })
    (bodyFinish := { bytes := artifactBytes, pos := 29791, limit := 29791 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code146_seq_146_tail0_decoded
  · rfl

#print axioms code146_decoded

@[cbv_eval] theorem code147_seq_147_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 29795, limit := 29808 } =
      .ok ((((Cache.raw.codes[147]!).body).drop 0, .end), { bytes := artifactBytes, pos := 29808, limit := 29808 }) := by
  cbv

theorem code147_decoded :
    code { bytes := artifactBytes, pos := 29791, limit := 30726 } =
      .ok (Cache.raw.codes[147]!, { bytes := artifactBytes, pos := 29808, limit := 30726 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 29792, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 29795, limit := 29808 })
    (bodyFinish := { bytes := artifactBytes, pos := 29808, limit := 29808 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code147_seq_147_tail0_decoded
  · rfl

#print axioms code147_decoded

@[cbv_eval] theorem code148_seq_148_tail0_decoded :
    instructionSequenceAt 83 false { bytes := artifactBytes, pos := 29812, limit := 29895 } =
      .ok ((((Cache.raw.codes[148]!).body).drop 0, .end), { bytes := artifactBytes, pos := 29895, limit := 29895 }) := by
  cbv

theorem code148_decoded :
    code { bytes := artifactBytes, pos := 29808, limit := 30726 } =
      .ok (Cache.raw.codes[148]!, { bytes := artifactBytes, pos := 29895, limit := 30726 }) := by
  refine code_eq_of_parts (size := 86)
    (payload := { bytes := artifactBytes, pos := 29809, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 29812, limit := 29895 })
    (bodyFinish := { bytes := artifactBytes, pos := 29895, limit := 29895 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code148_seq_148_tail0_decoded
  · rfl

#print axioms code148_decoded

@[cbv_eval] theorem code149_seq_149_18_t_0_t_tail18_decoded :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 29972, limit := 30262 } =
      .ok ((((((((Cache.raw.codes[149]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 30100, limit := 30262 }) := by
  cbv

@[cbv_eval] theorem code149_seq_149_18_t_0_t_tail0_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 29941, limit := 30262 } =
      .ok ((((((((Cache.raw.codes[149]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 30100, limit := 30262 }) := by
  cbv

@[cbv_eval] theorem code149_seq_149_18_t_tail0_decoded :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 29939, limit := 30262 } =
      .ok ((((((Cache.raw.codes[149]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 30101, limit := 30262 }) := by
  cbv

@[cbv_eval] theorem code149_seq_149_22_t_tail8_decoded :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 30121, limit := 30262 } =
      .ok ((((((Cache.raw.codes[149]!).body)[22]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 30252, limit := 30262 }) := by
  cbv

@[cbv_eval] theorem code149_seq_149_22_t_tail0_decoded :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 30108, limit := 30262 } =
      .ok ((((((Cache.raw.codes[149]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 30252, limit := 30262 }) := by
  cbv

@[cbv_eval] theorem code149_seq_149_tail22_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 30106, limit := 30262 } =
      .ok ((((Cache.raw.codes[149]!).body).drop 22, .end), { bytes := artifactBytes, pos := 30262, limit := 30262 }) := by
  cbv

@[cbv_eval] theorem code149_seq_149_tail18_decoded :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 29937, limit := 30262 } =
      .ok ((((Cache.raw.codes[149]!).body).drop 18, .end), { bytes := artifactBytes, pos := 30262, limit := 30262 }) := by
  cbv

@[cbv_eval] theorem code149_seq_149_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 29900, limit := 30262 } =
      .ok ((((Cache.raw.codes[149]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30262, limit := 30262 }) := by
  cbv


end Project.EulerReconstructed.Artifact
