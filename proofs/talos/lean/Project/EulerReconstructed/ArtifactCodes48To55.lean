import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code48_seq_48_tail0_decoded :
    instructionSequenceAt 27 false { bytes := artifactBytes, pos := 6523, limit := 6550 } =
      .ok ((((Cache.raw.codes[48]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6550, limit := 6550 }) := by
  cbv

theorem code48_decoded :
    code { bytes := artifactBytes, pos := 6519, limit := 30726 } =
      .ok (Cache.raw.codes[48]!, { bytes := artifactBytes, pos := 6550, limit := 30726 }) := by
  refine code_eq_of_parts (size := 30)
    (payload := { bytes := artifactBytes, pos := 6520, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 6523, limit := 6550 })
    (bodyFinish := { bytes := artifactBytes, pos := 6550, limit := 6550 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code48_seq_48_tail0_decoded
  · rfl

#print axioms code48_decoded

@[cbv_eval] theorem code49_seq_49_tail0_decoded :
    instructionSequenceAt 82 false { bytes := artifactBytes, pos := 6554, limit := 6636 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6636, limit := 6636 }) := by
  cbv

theorem code49_decoded :
    code { bytes := artifactBytes, pos := 6550, limit := 30726 } =
      .ok (Cache.raw.codes[49]!, { bytes := artifactBytes, pos := 6636, limit := 30726 }) := by
  refine code_eq_of_parts (size := 85)
    (payload := { bytes := artifactBytes, pos := 6551, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 6554, limit := 6636 })
    (bodyFinish := { bytes := artifactBytes, pos := 6636, limit := 6636 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code49_seq_49_tail0_decoded
  · rfl

#print axioms code49_decoded

@[cbv_eval] theorem code50_seq_50_tail0_decoded :
    instructionSequenceAt 59 false { bytes := artifactBytes, pos := 6640, limit := 6699 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6699, limit := 6699 }) := by
  cbv

theorem code50_decoded :
    code { bytes := artifactBytes, pos := 6636, limit := 30726 } =
      .ok (Cache.raw.codes[50]!, { bytes := artifactBytes, pos := 6699, limit := 30726 }) := by
  refine code_eq_of_parts (size := 62)
    (payload := { bytes := artifactBytes, pos := 6637, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 6640, limit := 6699 })
    (bodyFinish := { bytes := artifactBytes, pos := 6699, limit := 6699 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code50_seq_50_tail0_decoded
  · rfl

#print axioms code50_decoded

@[cbv_eval] theorem code51_seq_51_tail0_decoded :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 6703, limit := 6758 } =
      .ok ((((Cache.raw.codes[51]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6758, limit := 6758 }) := by
  cbv

theorem code51_decoded :
    code { bytes := artifactBytes, pos := 6699, limit := 30726 } =
      .ok (Cache.raw.codes[51]!, { bytes := artifactBytes, pos := 6758, limit := 30726 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 6700, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 6703, limit := 6758 })
    (bodyFinish := { bytes := artifactBytes, pos := 6758, limit := 6758 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code51_seq_51_tail0_decoded
  · rfl

#print axioms code51_decoded

@[cbv_eval] theorem code52_seq_52_16_t_tail26_decoded :
    instructionSequenceAt 245 true { bytes := artifactBytes, pos := 6896, limit := 7052 } =
      .ok ((((((Cache.raw.codes[52]!).body)[16]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 7032, limit := 7052 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_16_t_tail0_decoded :
    instructionSequenceAt 271 true { bytes := artifactBytes, pos := 6836, limit := 7052 } =
      .ok ((((((Cache.raw.codes[52]!).body)[16]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 7032, limit := 7052 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_tail16_decoded :
    instructionSequenceAt 273 false { bytes := artifactBytes, pos := 6834, limit := 7052 } =
      .ok ((((Cache.raw.codes[52]!).body).drop 16, .end), { bytes := artifactBytes, pos := 7052, limit := 7052 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_tail0_decoded :
    instructionSequenceAt 289 false { bytes := artifactBytes, pos := 6763, limit := 7052 } =
      .ok ((((Cache.raw.codes[52]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7052, limit := 7052 }) := by
  cbv

theorem code52_decoded :
    code { bytes := artifactBytes, pos := 6758, limit := 30726 } =
      .ok (Cache.raw.codes[52]!, { bytes := artifactBytes, pos := 7052, limit := 30726 }) := by
  refine code_eq_of_parts (size := 292)
    (payload := { bytes := artifactBytes, pos := 6760, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 6763, limit := 7052 })
    (bodyFinish := { bytes := artifactBytes, pos := 7052, limit := 7052 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code52_seq_52_tail0_decoded
  · rfl

#print axioms code52_decoded

@[cbv_eval] theorem code53_seq_53_tail3_decoded :
    instructionSequenceAt 135 false { bytes := artifactBytes, pos := 7062, limit := 7195 } =
      .ok ((((Cache.raw.codes[53]!).body).drop 3, .end), { bytes := artifactBytes, pos := 7195, limit := 7195 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_tail0_decoded :
    instructionSequenceAt 138 false { bytes := artifactBytes, pos := 7057, limit := 7195 } =
      .ok ((((Cache.raw.codes[53]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7195, limit := 7195 }) := by
  cbv

theorem code53_decoded :
    code { bytes := artifactBytes, pos := 7052, limit := 30726 } =
      .ok (Cache.raw.codes[53]!, { bytes := artifactBytes, pos := 7195, limit := 30726 }) := by
  refine code_eq_of_parts (size := 141)
    (payload := { bytes := artifactBytes, pos := 7054, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 7057, limit := 7195 })
    (bodyFinish := { bytes := artifactBytes, pos := 7195, limit := 7195 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code53_seq_53_tail0_decoded
  · rfl

#print axioms code53_decoded

@[cbv_eval] theorem code54_seq_54_tail20_decoded :
    instructionSequenceAt 210 false { bytes := artifactBytes, pos := 7302, limit := 7430 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 20, .end), { bytes := artifactBytes, pos := 7430, limit := 7430 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_tail0_decoded :
    instructionSequenceAt 230 false { bytes := artifactBytes, pos := 7200, limit := 7430 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7430, limit := 7430 }) := by
  cbv

theorem code54_decoded :
    code { bytes := artifactBytes, pos := 7195, limit := 30726 } =
      .ok (Cache.raw.codes[54]!, { bytes := artifactBytes, pos := 7430, limit := 30726 }) := by
  refine code_eq_of_parts (size := 233)
    (payload := { bytes := artifactBytes, pos := 7197, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 7200, limit := 7430 })
    (bodyFinish := { bytes := artifactBytes, pos := 7430, limit := 7430 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code54_seq_54_tail0_decoded
  · rfl

#print axioms code54_decoded

@[cbv_eval] theorem code55_seq_55_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 7434, limit := 7441 } =
      .ok ((((Cache.raw.codes[55]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7441, limit := 7441 }) := by
  cbv

theorem code55_decoded :
    code { bytes := artifactBytes, pos := 7430, limit := 30726 } =
      .ok (Cache.raw.codes[55]!, { bytes := artifactBytes, pos := 7441, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 7431, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 7434, limit := 7441 })
    (bodyFinish := { bytes := artifactBytes, pos := 7441, limit := 7441 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code55_seq_55_tail0_decoded
  · rfl

#print axioms code55_decoded


end Project.EulerReconstructed.Artifact
