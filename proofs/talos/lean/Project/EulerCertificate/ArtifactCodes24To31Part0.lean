import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code24_seq_24_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 8180, limit := 8187 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8187, limit := 8187 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 8176, limit := 45644 } =
      .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 8187, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 8177, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8180, limit := 8187 })
    (bodyFinish := { bytes := artifactBytes, pos := 8187, limit := 8187 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code24_seq_24_tail0_decoded
  · rfl

#print axioms code24_decoded

@[cbv_eval] theorem code25_seq_25_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 8191, limit := 8198 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8198, limit := 8198 }) := by
  cbv

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 8187, limit := 45644 } =
      .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 8198, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 8188, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8191, limit := 8198 })
    (bodyFinish := { bytes := artifactBytes, pos := 8198, limit := 8198 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code25_seq_25_tail0_decoded
  · rfl

#print axioms code25_decoded

@[cbv_eval] theorem code26_seq_26_tail122_decoded :
    instructionSequenceAt 251 false { bytes := artifactBytes, pos := 8447, limit := 8576 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 122, .end), { bytes := artifactBytes, pos := 8576, limit := 8576 }) := by
  cbv

@[cbv_eval] theorem code26_seq_26_tail58_decoded :
    instructionSequenceAt 315 false { bytes := artifactBytes, pos := 8319, limit := 8576 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 58, .end), { bytes := artifactBytes, pos := 8576, limit := 8576 }) := by
  cbv

@[cbv_eval] theorem code26_seq_26_tail0_decoded :
    instructionSequenceAt 373 false { bytes := artifactBytes, pos := 8203, limit := 8576 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8576, limit := 8576 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 8198, limit := 45644 } =
      .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 8576, limit := 45644 }) := by
  refine code_eq_of_parts (size := 376)
    (payload := { bytes := artifactBytes, pos := 8200, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8203, limit := 8576 })
    (bodyFinish := { bytes := artifactBytes, pos := 8576, limit := 8576 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code26_seq_26_tail0_decoded
  · rfl

#print axioms code26_decoded

@[cbv_eval] theorem code27_seq_27_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 8580, limit := 8618 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8618, limit := 8618 }) := by
  cbv

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 8576, limit := 45644 } =
      .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 8618, limit := 45644 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 8577, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8580, limit := 8618 })
    (bodyFinish := { bytes := artifactBytes, pos := 8618, limit := 8618 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code27_seq_27_tail0_decoded
  · rfl

#print axioms code27_decoded

@[cbv_eval] theorem code28_seq_28_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 8622, limit := 8641 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8641, limit := 8641 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 8618, limit := 45644 } =
      .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 8641, limit := 45644 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 8619, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8622, limit := 8641 })
    (bodyFinish := { bytes := artifactBytes, pos := 8641, limit := 8641 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code28_seq_28_tail0_decoded
  · rfl

#print axioms code28_decoded

@[cbv_eval] theorem code29_seq_29_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 8645, limit := 8678 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8678, limit := 8678 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 8641, limit := 45644 } =
      .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 8678, limit := 45644 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 8642, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8645, limit := 8678 })
    (bodyFinish := { bytes := artifactBytes, pos := 8678, limit := 8678 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code29_seq_29_tail0_decoded
  · rfl

#print axioms code29_decoded

@[cbv_eval] theorem code30_seq_30_tail0_decoded :
    instructionSequenceAt 124 false { bytes := artifactBytes, pos := 8682, limit := 8806 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8806, limit := 8806 }) := by
  cbv

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 8678, limit := 45644 } =
      .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 8806, limit := 45644 }) := by
  refine code_eq_of_parts (size := 127)
    (payload := { bytes := artifactBytes, pos := 8679, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8682, limit := 8806 })
    (bodyFinish := { bytes := artifactBytes, pos := 8806, limit := 8806 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code30_seq_30_tail0_decoded
  · rfl

#print axioms code30_decoded

end Project.EulerCertificate.Artifact
