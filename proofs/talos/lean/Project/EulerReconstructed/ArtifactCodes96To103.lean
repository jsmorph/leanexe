import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code96_seq_96_17_t_tail0_decoded :
    instructionSequenceAt 220 true { bytes := artifactBytes, pos := 13945, limit := 14093 } =
      .ok ((((((Cache.raw.codes[96]!).body)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 14073, limit := 14093 }) := by
  cbv

@[cbv_eval] theorem code96_seq_96_tail17_decoded :
    instructionSequenceAt 222 false { bytes := artifactBytes, pos := 13943, limit := 14093 } =
      .ok ((((Cache.raw.codes[96]!).body).drop 17, .end), { bytes := artifactBytes, pos := 14093, limit := 14093 }) := by
  cbv

@[cbv_eval] theorem code96_seq_96_tail0_decoded :
    instructionSequenceAt 239 false { bytes := artifactBytes, pos := 13854, limit := 14093 } =
      .ok ((((Cache.raw.codes[96]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14093, limit := 14093 }) := by
  cbv

theorem code96_decoded :
    code { bytes := artifactBytes, pos := 13849, limit := 30726 } =
      .ok (Cache.raw.codes[96]!, { bytes := artifactBytes, pos := 14093, limit := 30726 }) := by
  refine code_eq_of_parts (size := 242)
    (payload := { bytes := artifactBytes, pos := 13851, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 13854, limit := 14093 })
    (bodyFinish := { bytes := artifactBytes, pos := 14093, limit := 14093 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code96_seq_96_tail0_decoded
  · rfl

#print axioms code96_decoded

@[cbv_eval] theorem code97_seq_97_tail0_decoded :
    instructionSequenceAt 43 false { bytes := artifactBytes, pos := 14097, limit := 14140 } =
      .ok ((((Cache.raw.codes[97]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14140, limit := 14140 }) := by
  cbv

theorem code97_decoded :
    code { bytes := artifactBytes, pos := 14093, limit := 30726 } =
      .ok (Cache.raw.codes[97]!, { bytes := artifactBytes, pos := 14140, limit := 30726 }) := by
  refine code_eq_of_parts (size := 46)
    (payload := { bytes := artifactBytes, pos := 14094, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 14097, limit := 14140 })
    (bodyFinish := { bytes := artifactBytes, pos := 14140, limit := 14140 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code97_seq_97_tail0_decoded
  · rfl

#print axioms code97_decoded

@[cbv_eval] theorem code98_seq_98_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 14144, limit := 14151 } =
      .ok ((((Cache.raw.codes[98]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14151, limit := 14151 }) := by
  cbv

theorem code98_decoded :
    code { bytes := artifactBytes, pos := 14140, limit := 30726 } =
      .ok (Cache.raw.codes[98]!, { bytes := artifactBytes, pos := 14151, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 14141, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 14144, limit := 14151 })
    (bodyFinish := { bytes := artifactBytes, pos := 14151, limit := 14151 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code98_seq_98_tail0_decoded
  · rfl

#print axioms code98_decoded

@[cbv_eval] theorem code99_seq_99_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 14155, limit := 14162 } =
      .ok ((((Cache.raw.codes[99]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14162, limit := 14162 }) := by
  cbv

theorem code99_decoded :
    code { bytes := artifactBytes, pos := 14151, limit := 30726 } =
      .ok (Cache.raw.codes[99]!, { bytes := artifactBytes, pos := 14162, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 14152, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 14155, limit := 14162 })
    (bodyFinish := { bytes := artifactBytes, pos := 14162, limit := 14162 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code99_seq_99_tail0_decoded
  · rfl

#print axioms code99_decoded

@[cbv_eval] theorem code100_seq_100_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 14166, limit := 14173 } =
      .ok ((((Cache.raw.codes[100]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14173, limit := 14173 }) := by
  cbv

theorem code100_decoded :
    code { bytes := artifactBytes, pos := 14162, limit := 30726 } =
      .ok (Cache.raw.codes[100]!, { bytes := artifactBytes, pos := 14173, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 14163, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 14166, limit := 14173 })
    (bodyFinish := { bytes := artifactBytes, pos := 14173, limit := 14173 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code100_seq_100_tail0_decoded
  · rfl

#print axioms code100_decoded

@[cbv_eval] theorem code101_seq_101_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 14177, limit := 14184 } =
      .ok ((((Cache.raw.codes[101]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14184, limit := 14184 }) := by
  cbv

theorem code101_decoded :
    code { bytes := artifactBytes, pos := 14173, limit := 30726 } =
      .ok (Cache.raw.codes[101]!, { bytes := artifactBytes, pos := 14184, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 14174, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 14177, limit := 14184 })
    (bodyFinish := { bytes := artifactBytes, pos := 14184, limit := 14184 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code101_seq_101_tail0_decoded
  · rfl

#print axioms code101_decoded

@[cbv_eval] theorem code102_seq_102_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 14188, limit := 14195 } =
      .ok ((((Cache.raw.codes[102]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14195, limit := 14195 }) := by
  cbv

theorem code102_decoded :
    code { bytes := artifactBytes, pos := 14184, limit := 30726 } =
      .ok (Cache.raw.codes[102]!, { bytes := artifactBytes, pos := 14195, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 14185, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 14188, limit := 14195 })
    (bodyFinish := { bytes := artifactBytes, pos := 14195, limit := 14195 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code102_seq_102_tail0_decoded
  · rfl

#print axioms code102_decoded

@[cbv_eval] theorem code103_seq_103_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 14199, limit := 14248 } =
      .ok ((((Cache.raw.codes[103]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14248, limit := 14248 }) := by
  cbv

theorem code103_decoded :
    code { bytes := artifactBytes, pos := 14195, limit := 30726 } =
      .ok (Cache.raw.codes[103]!, { bytes := artifactBytes, pos := 14248, limit := 30726 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 14196, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 14199, limit := 14248 })
    (bodyFinish := { bytes := artifactBytes, pos := 14248, limit := 14248 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code103_seq_103_tail0_decoded
  · rfl

#print axioms code103_decoded


end Project.EulerReconstructed.Artifact
