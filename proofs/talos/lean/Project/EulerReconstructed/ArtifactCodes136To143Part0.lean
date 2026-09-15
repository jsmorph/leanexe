import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code136_seq_136_tail0_decoded :
    instructionSequenceAt 76 false { bytes := artifactBytes, pos := 20869, limit := 20945 } =
      .ok ((((Cache.raw.codes[136]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20945, limit := 20945 }) := by
  cbv

theorem code136_decoded :
    code { bytes := artifactBytes, pos := 20865, limit := 30726 } =
      .ok (Cache.raw.codes[136]!, { bytes := artifactBytes, pos := 20945, limit := 30726 }) := by
  refine code_eq_of_parts (size := 79)
    (payload := { bytes := artifactBytes, pos := 20866, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 20869, limit := 20945 })
    (bodyFinish := { bytes := artifactBytes, pos := 20945, limit := 20945 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code136_seq_136_tail0_decoded
  · rfl

#print axioms code136_decoded

@[cbv_eval] theorem code137_seq_137_tail125_decoded :
    instructionSequenceAt 270 false { bytes := artifactBytes, pos := 21216, limit := 21345 } =
      .ok ((((Cache.raw.codes[137]!).body).drop 125, .end), { bytes := artifactBytes, pos := 21345, limit := 21345 }) := by
  cbv

@[cbv_eval] theorem code137_seq_137_tail65_decoded :
    instructionSequenceAt 330 false { bytes := artifactBytes, pos := 21088, limit := 21345 } =
      .ok ((((Cache.raw.codes[137]!).body).drop 65, .end), { bytes := artifactBytes, pos := 21345, limit := 21345 }) := by
  cbv

@[cbv_eval] theorem code137_seq_137_tail4_decoded :
    instructionSequenceAt 391 false { bytes := artifactBytes, pos := 20959, limit := 21345 } =
      .ok ((((Cache.raw.codes[137]!).body).drop 4, .end), { bytes := artifactBytes, pos := 21345, limit := 21345 }) := by
  cbv

@[cbv_eval] theorem code137_seq_137_tail0_decoded :
    instructionSequenceAt 395 false { bytes := artifactBytes, pos := 20950, limit := 21345 } =
      .ok ((((Cache.raw.codes[137]!).body).drop 0, .end), { bytes := artifactBytes, pos := 21345, limit := 21345 }) := by
  cbv

theorem code137_decoded :
    code { bytes := artifactBytes, pos := 20945, limit := 30726 } =
      .ok (Cache.raw.codes[137]!, { bytes := artifactBytes, pos := 21345, limit := 30726 }) := by
  refine code_eq_of_parts (size := 398)
    (payload := { bytes := artifactBytes, pos := 20947, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 20950, limit := 21345 })
    (bodyFinish := { bytes := artifactBytes, pos := 21345, limit := 21345 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code137_seq_137_tail0_decoded
  · rfl

#print axioms code137_decoded

@[cbv_eval] theorem code138_seq_138_21_t_69_t_37_t_tail54_decoded :
    instructionSequenceAt 649 true { bytes := artifactBytes, pos := 21886, limit := 22186 } =
      .ok ((((((((((Cache.raw.codes[138]!).body)[21]!).childBody false)[69]!).childBody false)[37]!).childBody false).drop 54, .otherwise), { bytes := artifactBytes, pos := 22014, limit := 22186 }) := by
  cbv

@[cbv_eval] theorem code138_seq_138_21_t_69_t_37_t_tail12_decoded :
    instructionSequenceAt 691 true { bytes := artifactBytes, pos := 21758, limit := 22186 } =
      .ok ((((((((((Cache.raw.codes[138]!).body)[21]!).childBody false)[69]!).childBody false)[37]!).childBody false).drop 12, .otherwise), { bytes := artifactBytes, pos := 22014, limit := 22186 }) := by
  cbv

@[cbv_eval] theorem code138_seq_138_21_t_69_t_37_t_tail0_decoded :
    instructionSequenceAt 703 true { bytes := artifactBytes, pos := 21739, limit := 22186 } =
      .ok ((((((((((Cache.raw.codes[138]!).body)[21]!).childBody false)[69]!).childBody false)[37]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 22014, limit := 22186 }) := by
  cbv

@[cbv_eval] theorem code138_seq_138_21_t_69_t_tail37_decoded :
    instructionSequenceAt 705 true { bytes := artifactBytes, pos := 21737, limit := 22186 } =
      .ok ((((((((Cache.raw.codes[138]!).body)[21]!).childBody false)[69]!).childBody false).drop 37, .otherwise), { bytes := artifactBytes, pos := 22066, limit := 22186 }) := by
  cbv

@[cbv_eval] theorem code138_seq_138_21_t_69_t_tail0_decoded :
    instructionSequenceAt 742 true { bytes := artifactBytes, pos := 21620, limit := 22186 } =
      .ok ((((((((Cache.raw.codes[138]!).body)[21]!).childBody false)[69]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 22066, limit := 22186 }) := by
  cbv

@[cbv_eval] theorem code138_seq_138_21_t_tail69_decoded :
    instructionSequenceAt 744 true { bytes := artifactBytes, pos := 21618, limit := 22186 } =
      .ok ((((((Cache.raw.codes[138]!).body)[21]!).childBody false).drop 69, .otherwise), { bytes := artifactBytes, pos := 22118, limit := 22186 }) := by
  cbv

@[cbv_eval] theorem code138_seq_138_21_t_tail56_decoded :
    instructionSequenceAt 757 true { bytes := artifactBytes, pos := 21487, limit := 22186 } =
      .ok ((((((Cache.raw.codes[138]!).body)[21]!).childBody false).drop 56, .otherwise), { bytes := artifactBytes, pos := 22118, limit := 22186 }) := by
  cbv

@[cbv_eval] theorem code138_seq_138_21_t_tail0_decoded :
    instructionSequenceAt 813 true { bytes := artifactBytes, pos := 21397, limit := 22186 } =
      .ok ((((((Cache.raw.codes[138]!).body)[21]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 22118, limit := 22186 }) := by
  cbv

@[cbv_eval] theorem code138_seq_138_tail21_decoded :
    instructionSequenceAt 815 false { bytes := artifactBytes, pos := 21395, limit := 22186 } =
      .ok ((((Cache.raw.codes[138]!).body).drop 21, .end), { bytes := artifactBytes, pos := 22186, limit := 22186 }) := by
  cbv


end Project.EulerReconstructed.Artifact
