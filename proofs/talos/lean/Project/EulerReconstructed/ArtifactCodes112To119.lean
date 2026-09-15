import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code112_seq_112_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 16419, limit := 16444 } =
      .ok ((((Cache.raw.codes[112]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16444, limit := 16444 }) := by
  cbv

theorem code112_decoded :
    code { bytes := artifactBytes, pos := 16415, limit := 30726 } =
      .ok (Cache.raw.codes[112]!, { bytes := artifactBytes, pos := 16444, limit := 30726 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 16416, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 16419, limit := 16444 })
    (bodyFinish := { bytes := artifactBytes, pos := 16444, limit := 16444 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code112_seq_112_tail0_decoded
  · rfl

#print axioms code112_decoded

@[cbv_eval] theorem code113_seq_113_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 16448, limit := 16473 } =
      .ok ((((Cache.raw.codes[113]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16473, limit := 16473 }) := by
  cbv

theorem code113_decoded :
    code { bytes := artifactBytes, pos := 16444, limit := 30726 } =
      .ok (Cache.raw.codes[113]!, { bytes := artifactBytes, pos := 16473, limit := 30726 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 16445, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 16448, limit := 16473 })
    (bodyFinish := { bytes := artifactBytes, pos := 16473, limit := 16473 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code113_seq_113_tail0_decoded
  · rfl

#print axioms code113_decoded

@[cbv_eval] theorem code114_seq_114_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 16477, limit := 16484 } =
      .ok ((((Cache.raw.codes[114]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16484, limit := 16484 }) := by
  cbv

theorem code114_decoded :
    code { bytes := artifactBytes, pos := 16473, limit := 30726 } =
      .ok (Cache.raw.codes[114]!, { bytes := artifactBytes, pos := 16484, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 16474, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 16477, limit := 16484 })
    (bodyFinish := { bytes := artifactBytes, pos := 16484, limit := 16484 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code114_seq_114_tail0_decoded
  · rfl

#print axioms code114_decoded

@[cbv_eval] theorem code115_seq_115_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 16488, limit := 16495 } =
      .ok ((((Cache.raw.codes[115]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16495, limit := 16495 }) := by
  cbv

theorem code115_decoded :
    code { bytes := artifactBytes, pos := 16484, limit := 30726 } =
      .ok (Cache.raw.codes[115]!, { bytes := artifactBytes, pos := 16495, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 16485, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 16488, limit := 16495 })
    (bodyFinish := { bytes := artifactBytes, pos := 16495, limit := 16495 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code115_seq_115_tail0_decoded
  · rfl

#print axioms code115_decoded

@[cbv_eval] theorem code116_seq_116_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 16499, limit := 16506 } =
      .ok ((((Cache.raw.codes[116]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16506, limit := 16506 }) := by
  cbv

theorem code116_decoded :
    code { bytes := artifactBytes, pos := 16495, limit := 30726 } =
      .ok (Cache.raw.codes[116]!, { bytes := artifactBytes, pos := 16506, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 16496, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 16499, limit := 16506 })
    (bodyFinish := { bytes := artifactBytes, pos := 16506, limit := 16506 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code116_seq_116_tail0_decoded
  · rfl

#print axioms code116_decoded

@[cbv_eval] theorem code117_seq_117_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 16510, limit := 16517 } =
      .ok ((((Cache.raw.codes[117]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16517, limit := 16517 }) := by
  cbv

theorem code117_decoded :
    code { bytes := artifactBytes, pos := 16506, limit := 30726 } =
      .ok (Cache.raw.codes[117]!, { bytes := artifactBytes, pos := 16517, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 16507, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 16510, limit := 16517 })
    (bodyFinish := { bytes := artifactBytes, pos := 16517, limit := 16517 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code117_seq_117_tail0_decoded
  · rfl

#print axioms code117_decoded

@[cbv_eval] theorem code118_seq_118_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 16521, limit := 16528 } =
      .ok ((((Cache.raw.codes[118]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16528, limit := 16528 }) := by
  cbv

theorem code118_decoded :
    code { bytes := artifactBytes, pos := 16517, limit := 30726 } =
      .ok (Cache.raw.codes[118]!, { bytes := artifactBytes, pos := 16528, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 16518, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 16521, limit := 16528 })
    (bodyFinish := { bytes := artifactBytes, pos := 16528, limit := 16528 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code118_seq_118_tail0_decoded
  · rfl

#print axioms code118_decoded

@[cbv_eval] theorem code119_seq_119_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 16532, limit := 16539 } =
      .ok ((((Cache.raw.codes[119]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16539, limit := 16539 }) := by
  cbv

theorem code119_decoded :
    code { bytes := artifactBytes, pos := 16528, limit := 30726 } =
      .ok (Cache.raw.codes[119]!, { bytes := artifactBytes, pos := 16539, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 16529, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 16532, limit := 16539 })
    (bodyFinish := { bytes := artifactBytes, pos := 16539, limit := 16539 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code119_seq_119_tail0_decoded
  · rfl

#print axioms code119_decoded


end Project.EulerReconstructed.Artifact
