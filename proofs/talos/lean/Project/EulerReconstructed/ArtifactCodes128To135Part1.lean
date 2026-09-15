import Project.EulerReconstructed.ArtifactCodes128To135Part0
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code130_seq_130_tail0_decoded :
    instructionSequenceAt 162 false { bytes := artifactBytes, pos := 20219, limit := 20381 } =
      .ok ((((Cache.raw.codes[130]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20381, limit := 20381 }) := by
  cbv

theorem code130_decoded :
    code { bytes := artifactBytes, pos := 20214, limit := 30726 } =
      .ok (Cache.raw.codes[130]!, { bytes := artifactBytes, pos := 20381, limit := 30726 }) := by
  refine code_eq_of_parts (size := 165)
    (payload := { bytes := artifactBytes, pos := 20216, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 20219, limit := 20381 })
    (bodyFinish := { bytes := artifactBytes, pos := 20381, limit := 20381 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code130_seq_130_tail0_decoded
  · rfl

#print axioms code130_decoded

@[cbv_eval] theorem code131_seq_131_tail0_decoded :
    instructionSequenceAt 109 false { bytes := artifactBytes, pos := 20385, limit := 20494 } =
      .ok ((((Cache.raw.codes[131]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20494, limit := 20494 }) := by
  cbv

theorem code131_decoded :
    code { bytes := artifactBytes, pos := 20381, limit := 30726 } =
      .ok (Cache.raw.codes[131]!, { bytes := artifactBytes, pos := 20494, limit := 30726 }) := by
  refine code_eq_of_parts (size := 112)
    (payload := { bytes := artifactBytes, pos := 20382, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 20385, limit := 20494 })
    (bodyFinish := { bytes := artifactBytes, pos := 20494, limit := 20494 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code131_seq_131_tail0_decoded
  · rfl

#print axioms code131_decoded

@[cbv_eval] theorem code132_seq_132_tail0_decoded :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 20498, limit := 20593 } =
      .ok ((((Cache.raw.codes[132]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20593, limit := 20593 }) := by
  cbv

theorem code132_decoded :
    code { bytes := artifactBytes, pos := 20494, limit := 30726 } =
      .ok (Cache.raw.codes[132]!, { bytes := artifactBytes, pos := 20593, limit := 30726 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 20495, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 20498, limit := 20593 })
    (bodyFinish := { bytes := artifactBytes, pos := 20593, limit := 20593 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code132_seq_132_tail0_decoded
  · rfl

#print axioms code132_decoded

@[cbv_eval] theorem code133_seq_133_tail0_decoded :
    instructionSequenceAt 92 false { bytes := artifactBytes, pos := 20597, limit := 20689 } =
      .ok ((((Cache.raw.codes[133]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20689, limit := 20689 }) := by
  cbv

theorem code133_decoded :
    code { bytes := artifactBytes, pos := 20593, limit := 30726 } =
      .ok (Cache.raw.codes[133]!, { bytes := artifactBytes, pos := 20689, limit := 30726 }) := by
  refine code_eq_of_parts (size := 95)
    (payload := { bytes := artifactBytes, pos := 20594, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 20597, limit := 20689 })
    (bodyFinish := { bytes := artifactBytes, pos := 20689, limit := 20689 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code133_seq_133_tail0_decoded
  · rfl

#print axioms code133_decoded

@[cbv_eval] theorem code134_seq_134_tail0_decoded :
    instructionSequenceAt 84 false { bytes := artifactBytes, pos := 20693, limit := 20777 } =
      .ok ((((Cache.raw.codes[134]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20777, limit := 20777 }) := by
  cbv

theorem code134_decoded :
    code { bytes := artifactBytes, pos := 20689, limit := 30726 } =
      .ok (Cache.raw.codes[134]!, { bytes := artifactBytes, pos := 20777, limit := 30726 }) := by
  refine code_eq_of_parts (size := 87)
    (payload := { bytes := artifactBytes, pos := 20690, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 20693, limit := 20777 })
    (bodyFinish := { bytes := artifactBytes, pos := 20777, limit := 20777 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code134_seq_134_tail0_decoded
  · rfl

#print axioms code134_decoded

@[cbv_eval] theorem code135_seq_135_tail0_decoded :
    instructionSequenceAt 84 false { bytes := artifactBytes, pos := 20781, limit := 20865 } =
      .ok ((((Cache.raw.codes[135]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20865, limit := 20865 }) := by
  cbv

theorem code135_decoded :
    code { bytes := artifactBytes, pos := 20777, limit := 30726 } =
      .ok (Cache.raw.codes[135]!, { bytes := artifactBytes, pos := 20865, limit := 30726 }) := by
  refine code_eq_of_parts (size := 87)
    (payload := { bytes := artifactBytes, pos := 20778, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 20781, limit := 20865 })
    (bodyFinish := { bytes := artifactBytes, pos := 20865, limit := 20865 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code135_seq_135_tail0_decoded
  · rfl

#print axioms code135_decoded
end Project.EulerReconstructed.Artifact
