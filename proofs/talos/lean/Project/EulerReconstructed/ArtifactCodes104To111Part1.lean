import Project.EulerReconstructed.ArtifactCodes104To111Part0
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code105_decoded :
    code { bytes := artifactBytes, pos := 15125, limit := 30726 } =
      .ok (Cache.raw.codes[105]!, { bytes := artifactBytes, pos := 15471, limit := 30726 }) := by
  refine code_eq_of_parts (size := 344)
    (payload := { bytes := artifactBytes, pos := 15127, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 15130, limit := 15471 })
    (bodyFinish := { bytes := artifactBytes, pos := 15471, limit := 15471 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code105_seq_105_tail0_decoded
  · rfl

#print axioms code105_decoded

@[cbv_eval] theorem code106_seq_106_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 15475, limit := 15500 } =
      .ok ((((Cache.raw.codes[106]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15500, limit := 15500 }) := by
  cbv

theorem code106_decoded :
    code { bytes := artifactBytes, pos := 15471, limit := 30726 } =
      .ok (Cache.raw.codes[106]!, { bytes := artifactBytes, pos := 15500, limit := 30726 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 15472, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 15475, limit := 15500 })
    (bodyFinish := { bytes := artifactBytes, pos := 15500, limit := 15500 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code106_seq_106_tail0_decoded
  · rfl

#print axioms code106_decoded

@[cbv_eval] theorem code107_seq_107_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 15504, limit := 15529 } =
      .ok ((((Cache.raw.codes[107]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15529, limit := 15529 }) := by
  cbv

theorem code107_decoded :
    code { bytes := artifactBytes, pos := 15500, limit := 30726 } =
      .ok (Cache.raw.codes[107]!, { bytes := artifactBytes, pos := 15529, limit := 30726 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 15501, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 15504, limit := 15529 })
    (bodyFinish := { bytes := artifactBytes, pos := 15529, limit := 15529 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code107_seq_107_tail0_decoded
  · rfl

#print axioms code107_decoded

@[cbv_eval] theorem code108_seq_108_204_t_tail43_decoded :
    instructionSequenceAt 544 true { bytes := artifactBytes, pos := 16099, limit := 16328 } =
      .ok ((((((Cache.raw.codes[108]!).body)[204]!).childBody false).drop 43, .otherwise), { bytes := artifactBytes, pos := 16228, limit := 16328 }) := by
  cbv

@[cbv_eval] theorem code108_seq_108_204_t_tail0_decoded :
    instructionSequenceAt 587 true { bytes := artifactBytes, pos := 15999, limit := 16328 } =
      .ok ((((((Cache.raw.codes[108]!).body)[204]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 16228, limit := 16328 }) := by
  cbv

@[cbv_eval] theorem code108_seq_108_tail204_decoded :
    instructionSequenceAt 589 false { bytes := artifactBytes, pos := 15997, limit := 16328 } =
      .ok ((((Cache.raw.codes[108]!).body).drop 204, .end), { bytes := artifactBytes, pos := 16328, limit := 16328 }) := by
  cbv

@[cbv_eval] theorem code108_seq_108_tail167_decoded :
    instructionSequenceAt 626 false { bytes := artifactBytes, pos := 15869, limit := 16328 } =
      .ok ((((Cache.raw.codes[108]!).body).drop 167, .end), { bytes := artifactBytes, pos := 16328, limit := 16328 }) := by
  cbv

@[cbv_eval] theorem code108_seq_108_tail103_decoded :
    instructionSequenceAt 690 false { bytes := artifactBytes, pos := 15741, limit := 16328 } =
      .ok ((((Cache.raw.codes[108]!).body).drop 103, .end), { bytes := artifactBytes, pos := 16328, limit := 16328 }) := by
  cbv

@[cbv_eval] theorem code108_seq_108_tail39_decoded :
    instructionSequenceAt 754 false { bytes := artifactBytes, pos := 15613, limit := 16328 } =
      .ok ((((Cache.raw.codes[108]!).body).drop 39, .end), { bytes := artifactBytes, pos := 16328, limit := 16328 }) := by
  cbv

@[cbv_eval] theorem code108_seq_108_tail0_decoded :
    instructionSequenceAt 793 false { bytes := artifactBytes, pos := 15535, limit := 16328 } =
      .ok ((((Cache.raw.codes[108]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16328, limit := 16328 }) := by
  cbv

theorem code108_decoded :
    code { bytes := artifactBytes, pos := 15529, limit := 30726 } =
      .ok (Cache.raw.codes[108]!, { bytes := artifactBytes, pos := 16328, limit := 30726 }) := by
  refine code_eq_of_parts (size := 797)
    (payload := { bytes := artifactBytes, pos := 15531, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 15535, limit := 16328 })
    (bodyFinish := { bytes := artifactBytes, pos := 16328, limit := 16328 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code108_seq_108_tail0_decoded
  · rfl

#print axioms code108_decoded

@[cbv_eval] theorem code109_seq_109_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 16332, limit := 16357 } =
      .ok ((((Cache.raw.codes[109]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16357, limit := 16357 }) := by
  cbv

theorem code109_decoded :
    code { bytes := artifactBytes, pos := 16328, limit := 30726 } =
      .ok (Cache.raw.codes[109]!, { bytes := artifactBytes, pos := 16357, limit := 30726 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 16329, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 16332, limit := 16357 })
    (bodyFinish := { bytes := artifactBytes, pos := 16357, limit := 16357 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code109_seq_109_tail0_decoded
  · rfl

#print axioms code109_decoded

@[cbv_eval] theorem code110_seq_110_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 16361, limit := 16386 } =
      .ok ((((Cache.raw.codes[110]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16386, limit := 16386 }) := by
  cbv


end Project.EulerReconstructed.Artifact
