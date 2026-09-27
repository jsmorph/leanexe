import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code56_seq_56_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 15456, limit := 15463 } =
      .ok ((((Cache.raw.codes[56]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15463, limit := 15463 }) := by
  cbv

theorem code56_decoded :
    code { bytes := artifactBytes, pos := 15452, limit := 45644 } =
      .ok (Cache.raw.codes[56]!, { bytes := artifactBytes, pos := 15463, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 15453, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 15456, limit := 15463 })
    (bodyFinish := { bytes := artifactBytes, pos := 15463, limit := 15463 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code56_seq_56_tail0_decoded
  · rfl

#print axioms code56_decoded

@[cbv_eval] theorem code57_seq_57_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 15467, limit := 15486 } =
      .ok ((((Cache.raw.codes[57]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15486, limit := 15486 }) := by
  cbv

theorem code57_decoded :
    code { bytes := artifactBytes, pos := 15463, limit := 45644 } =
      .ok (Cache.raw.codes[57]!, { bytes := artifactBytes, pos := 15486, limit := 45644 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 15464, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 15467, limit := 15486 })
    (bodyFinish := { bytes := artifactBytes, pos := 15486, limit := 15486 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code57_seq_57_tail0_decoded
  · rfl

#print axioms code57_decoded

@[cbv_eval] theorem code58_seq_58_tail0_decoded :
    instructionSequenceAt 106 false { bytes := artifactBytes, pos := 15490, limit := 15596 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15596, limit := 15596 }) := by
  cbv

theorem code58_decoded :
    code { bytes := artifactBytes, pos := 15486, limit := 45644 } =
      .ok (Cache.raw.codes[58]!, { bytes := artifactBytes, pos := 15596, limit := 45644 }) := by
  refine code_eq_of_parts (size := 109)
    (payload := { bytes := artifactBytes, pos := 15487, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 15490, limit := 15596 })
    (bodyFinish := { bytes := artifactBytes, pos := 15596, limit := 15596 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code58_seq_58_tail0_decoded
  · rfl

#print axioms code58_decoded

@[cbv_eval] theorem code59_seq_59_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 15600, limit := 15665 } =
      .ok ((((Cache.raw.codes[59]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15665, limit := 15665 }) := by
  cbv

theorem code59_decoded :
    code { bytes := artifactBytes, pos := 15596, limit := 45644 } =
      .ok (Cache.raw.codes[59]!, { bytes := artifactBytes, pos := 15665, limit := 45644 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 15597, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 15600, limit := 15665 })
    (bodyFinish := { bytes := artifactBytes, pos := 15665, limit := 15665 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code59_seq_59_tail0_decoded
  · rfl

#print axioms code59_decoded

@[cbv_eval] theorem code60_seq_60_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 15669, limit := 15734 } =
      .ok ((((Cache.raw.codes[60]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15734, limit := 15734 }) := by
  cbv

theorem code60_decoded :
    code { bytes := artifactBytes, pos := 15665, limit := 45644 } =
      .ok (Cache.raw.codes[60]!, { bytes := artifactBytes, pos := 15734, limit := 45644 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 15666, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 15669, limit := 15734 })
    (bodyFinish := { bytes := artifactBytes, pos := 15734, limit := 15734 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code60_seq_60_tail0_decoded
  · rfl

#print axioms code60_decoded

@[cbv_eval] theorem code61_seq_61_tail0_decoded :
    instructionSequenceAt 52 false { bytes := artifactBytes, pos := 15738, limit := 15790 } =
      .ok ((((Cache.raw.codes[61]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15790, limit := 15790 }) := by
  cbv

theorem code61_decoded :
    code { bytes := artifactBytes, pos := 15734, limit := 45644 } =
      .ok (Cache.raw.codes[61]!, { bytes := artifactBytes, pos := 15790, limit := 45644 }) := by
  refine code_eq_of_parts (size := 55)
    (payload := { bytes := artifactBytes, pos := 15735, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 15738, limit := 15790 })
    (bodyFinish := { bytes := artifactBytes, pos := 15790, limit := 15790 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code61_seq_61_tail0_decoded
  · rfl

#print axioms code61_decoded

@[cbv_eval] theorem code62_seq_62_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 15794, limit := 15807 } =
      .ok ((((Cache.raw.codes[62]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15807, limit := 15807 }) := by
  cbv

theorem code62_decoded :
    code { bytes := artifactBytes, pos := 15790, limit := 45644 } =
      .ok (Cache.raw.codes[62]!, { bytes := artifactBytes, pos := 15807, limit := 45644 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 15791, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 15794, limit := 15807 })
    (bodyFinish := { bytes := artifactBytes, pos := 15807, limit := 15807 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code62_seq_62_tail0_decoded
  · rfl

#print axioms code62_decoded

@[cbv_eval] theorem code63_seq_63_tail0_decoded :
    instructionSequenceAt 123 false { bytes := artifactBytes, pos := 15811, limit := 15934 } =
      .ok ((((Cache.raw.codes[63]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15934, limit := 15934 }) := by
  cbv

theorem code63_decoded :
    code { bytes := artifactBytes, pos := 15807, limit := 45644 } =
      .ok (Cache.raw.codes[63]!, { bytes := artifactBytes, pos := 15934, limit := 45644 }) := by
  refine code_eq_of_parts (size := 126)
    (payload := { bytes := artifactBytes, pos := 15808, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 15811, limit := 15934 })
    (bodyFinish := { bytes := artifactBytes, pos := 15934, limit := 15934 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code63_seq_63_tail0_decoded
  · rfl

#print axioms code63_decoded

end Project.EulerCertificate.Artifact
