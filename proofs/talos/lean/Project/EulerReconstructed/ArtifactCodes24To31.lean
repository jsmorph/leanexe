import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code24_seq_24_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 3624, limit := 3689 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3689, limit := 3689 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 3620, limit := 30726 } =
      .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 3689, limit := 30726 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 3621, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 3624, limit := 3689 })
    (bodyFinish := { bytes := artifactBytes, pos := 3689, limit := 3689 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code24_seq_24_tail0_decoded
  · rfl

#print axioms code24_decoded

@[cbv_eval] theorem code25_seq_25_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 3693, limit := 3758 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3758, limit := 3758 }) := by
  cbv

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 3689, limit := 30726 } =
      .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 3758, limit := 30726 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 3690, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 3693, limit := 3758 })
    (bodyFinish := { bytes := artifactBytes, pos := 3758, limit := 3758 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code25_seq_25_tail0_decoded
  · rfl

#print axioms code25_decoded

@[cbv_eval] theorem code26_seq_26_tail0_decoded :
    instructionSequenceAt 52 false { bytes := artifactBytes, pos := 3762, limit := 3814 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3814, limit := 3814 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 3758, limit := 30726 } =
      .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 3814, limit := 30726 }) := by
  refine code_eq_of_parts (size := 55)
    (payload := { bytes := artifactBytes, pos := 3759, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 3762, limit := 3814 })
    (bodyFinish := { bytes := artifactBytes, pos := 3814, limit := 3814 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code26_seq_26_tail0_decoded
  · rfl

#print axioms code26_decoded

@[cbv_eval] theorem code27_seq_27_tail0_decoded :
    instructionSequenceAt 123 false { bytes := artifactBytes, pos := 3818, limit := 3941 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3941, limit := 3941 }) := by
  cbv

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 3814, limit := 30726 } =
      .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 3941, limit := 30726 }) := by
  refine code_eq_of_parts (size := 126)
    (payload := { bytes := artifactBytes, pos := 3815, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 3818, limit := 3941 })
    (bodyFinish := { bytes := artifactBytes, pos := 3941, limit := 3941 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code27_seq_27_tail0_decoded
  · rfl

#print axioms code27_decoded

@[cbv_eval] theorem code28_seq_28_tail0_decoded :
    instructionSequenceAt 125 false { bytes := artifactBytes, pos := 3946, limit := 4071 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4071, limit := 4071 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 3941, limit := 30726 } =
      .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 4071, limit := 30726 }) := by
  refine code_eq_of_parts (size := 128)
    (payload := { bytes := artifactBytes, pos := 3943, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 3946, limit := 4071 })
    (bodyFinish := { bytes := artifactBytes, pos := 4071, limit := 4071 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code28_seq_28_tail0_decoded
  · rfl

#print axioms code28_decoded

@[cbv_eval] theorem code29_seq_29_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 4075, limit := 4183 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4183, limit := 4183 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 4071, limit := 30726 } =
      .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 4183, limit := 30726 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 4072, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 4075, limit := 4183 })
    (bodyFinish := { bytes := artifactBytes, pos := 4183, limit := 4183 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code29_seq_29_tail0_decoded
  · rfl

#print axioms code29_decoded

@[cbv_eval] theorem code30_seq_30_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 4187, limit := 4295 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4295, limit := 4295 }) := by
  cbv

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 4183, limit := 30726 } =
      .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 4295, limit := 30726 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 4184, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 4187, limit := 4295 })
    (bodyFinish := { bytes := artifactBytes, pos := 4295, limit := 4295 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code30_seq_30_tail0_decoded
  · rfl

#print axioms code30_decoded

@[cbv_eval] theorem code31_seq_31_47_t_tail26_decoded :
    instructionSequenceAt 271 true { bytes := artifactBytes, pos := 4489, limit := 4646 } =
      .ok ((((((Cache.raw.codes[31]!).body)[47]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 4626, limit := 4646 }) := by
  cbv

@[cbv_eval] theorem code31_seq_31_47_t_tail0_decoded :
    instructionSequenceAt 297 true { bytes := artifactBytes, pos := 4429, limit := 4646 } =
      .ok ((((((Cache.raw.codes[31]!).body)[47]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4626, limit := 4646 }) := by
  cbv

@[cbv_eval] theorem code31_seq_31_tail47_decoded :
    instructionSequenceAt 299 false { bytes := artifactBytes, pos := 4427, limit := 4646 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 47, .end), { bytes := artifactBytes, pos := 4646, limit := 4646 }) := by
  cbv

@[cbv_eval] theorem code31_seq_31_tail0_decoded :
    instructionSequenceAt 346 false { bytes := artifactBytes, pos := 4300, limit := 4646 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4646, limit := 4646 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 4295, limit := 30726 } =
      .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 4646, limit := 30726 }) := by
  refine code_eq_of_parts (size := 349)
    (payload := { bytes := artifactBytes, pos := 4297, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 4300, limit := 4646 })
    (bodyFinish := { bytes := artifactBytes, pos := 4646, limit := 4646 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code31_seq_31_tail0_decoded
  · rfl

#print axioms code31_decoded


end Project.EulerReconstructed.Artifact
