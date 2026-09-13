import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactByteLookup
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.Evaluate

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code57_tail0_decoded :
    instructionSequenceAt 239 false { bytes := artifactBytes, pos := 6983, limit := 7222 } =
      .ok (((Cache.raw.codes[57]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 7222, limit := 7222 }) := by
  cbv

theorem code57_decoded :
    code { bytes := artifactBytes, pos := 6978, limit := 21767 } =
      .ok (Cache.raw.codes[57]!, { bytes := artifactBytes, pos := 7222, limit := 21767 }) := by
  refine code_eq_of_parts (size := 242)
    (payload := { bytes := artifactBytes, pos := 6980, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 6983, limit := 7222 })
    (bodyFinish := { bytes := artifactBytes, pos := 7222, limit := 7222 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code57_tail0_decoded
  · rfl

#print axioms code57_decoded

@[cbv_eval] theorem code58_tail0_decoded :
    instructionSequenceAt 43 false { bytes := artifactBytes, pos := 7226, limit := 7269 } =
      .ok (((Cache.raw.codes[58]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 7269, limit := 7269 }) := by
  cbv

theorem code58_decoded :
    code { bytes := artifactBytes, pos := 7222, limit := 21767 } =
      .ok (Cache.raw.codes[58]!, { bytes := artifactBytes, pos := 7269, limit := 21767 }) := by
  refine code_eq_of_parts (size := 46)
    (payload := { bytes := artifactBytes, pos := 7223, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 7226, limit := 7269 })
    (bodyFinish := { bytes := artifactBytes, pos := 7269, limit := 7269 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code58_tail0_decoded
  · rfl

#print axioms code58_decoded

@[cbv_eval] theorem code59_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 7273, limit := 7280 } =
      .ok (((Cache.raw.codes[59]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 7280, limit := 7280 }) := by
  cbv

theorem code59_decoded :
    code { bytes := artifactBytes, pos := 7269, limit := 21767 } =
      .ok (Cache.raw.codes[59]!, { bytes := artifactBytes, pos := 7280, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 7270, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 7273, limit := 7280 })
    (bodyFinish := { bytes := artifactBytes, pos := 7280, limit := 7280 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code59_tail0_decoded
  · rfl

#print axioms code59_decoded

@[cbv_eval] theorem code60_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 7284, limit := 7291 } =
      .ok (((Cache.raw.codes[60]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 7291, limit := 7291 }) := by
  cbv

theorem code60_decoded :
    code { bytes := artifactBytes, pos := 7280, limit := 21767 } =
      .ok (Cache.raw.codes[60]!, { bytes := artifactBytes, pos := 7291, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 7281, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 7284, limit := 7291 })
    (bodyFinish := { bytes := artifactBytes, pos := 7291, limit := 7291 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code60_tail0_decoded
  · rfl

#print axioms code60_decoded

@[cbv_eval] theorem code61_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 7295, limit := 7302 } =
      .ok (((Cache.raw.codes[61]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 7302, limit := 7302 }) := by
  cbv

theorem code61_decoded :
    code { bytes := artifactBytes, pos := 7291, limit := 21767 } =
      .ok (Cache.raw.codes[61]!, { bytes := artifactBytes, pos := 7302, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 7292, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 7295, limit := 7302 })
    (bodyFinish := { bytes := artifactBytes, pos := 7302, limit := 7302 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code61_tail0_decoded
  · rfl

#print axioms code61_decoded

@[cbv_eval] theorem code62_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 7306, limit := 7313 } =
      .ok (((Cache.raw.codes[62]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 7313, limit := 7313 }) := by
  cbv

theorem code62_decoded :
    code { bytes := artifactBytes, pos := 7302, limit := 21767 } =
      .ok (Cache.raw.codes[62]!, { bytes := artifactBytes, pos := 7313, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 7303, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 7306, limit := 7313 })
    (bodyFinish := { bytes := artifactBytes, pos := 7313, limit := 7313 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code62_tail0_decoded
  · rfl

#print axioms code62_decoded

@[cbv_eval] theorem code63_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 7317, limit := 7324 } =
      .ok (((Cache.raw.codes[63]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 7324, limit := 7324 }) := by
  cbv

theorem code63_decoded :
    code { bytes := artifactBytes, pos := 7313, limit := 21767 } =
      .ok (Cache.raw.codes[63]!, { bytes := artifactBytes, pos := 7324, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 7314, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 7317, limit := 7324 })
    (bodyFinish := { bytes := artifactBytes, pos := 7324, limit := 7324 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code63_tail0_decoded
  · rfl

#print axioms code63_decoded

@[cbv_eval] theorem code64_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 7328, limit := 7377 } =
      .ok (((Cache.raw.codes[64]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 7377, limit := 7377 }) := by
  cbv

theorem code64_decoded :
    code { bytes := artifactBytes, pos := 7324, limit := 21767 } =
      .ok (Cache.raw.codes[64]!, { bytes := artifactBytes, pos := 7377, limit := 21767 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 7325, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 7328, limit := 7377 })
    (bodyFinish := { bytes := artifactBytes, pos := 7377, limit := 7377 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code64_tail0_decoded
  · rfl

#print axioms code64_decoded

@[cbv_eval] theorem code66_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 8557, limit := 8582 } =
      .ok (((Cache.raw.codes[66]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 8582, limit := 8582 }) := by
  cbv

theorem code66_decoded :
    code { bytes := artifactBytes, pos := 8553, limit := 21767 } =
      .ok (Cache.raw.codes[66]!, { bytes := artifactBytes, pos := 8582, limit := 21767 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 8554, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 8557, limit := 8582 })
    (bodyFinish := { bytes := artifactBytes, pos := 8582, limit := 8582 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code66_tail0_decoded
  · rfl

#print axioms code66_decoded

@[cbv_eval] theorem code67_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 8586, limit := 8611 } =
      .ok (((Cache.raw.codes[67]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 8611, limit := 8611 }) := by
  cbv

theorem code67_decoded :
    code { bytes := artifactBytes, pos := 8582, limit := 21767 } =
      .ok (Cache.raw.codes[67]!, { bytes := artifactBytes, pos := 8611, limit := 21767 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 8583, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 8586, limit := 8611 })
    (bodyFinish := { bytes := artifactBytes, pos := 8611, limit := 8611 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code67_tail0_decoded
  · rfl

#print axioms code67_decoded

@[cbv_eval] theorem code68_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 8615, limit := 8640 } =
      .ok (((Cache.raw.codes[68]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 8640, limit := 8640 }) := by
  cbv

theorem code68_decoded :
    code { bytes := artifactBytes, pos := 8611, limit := 21767 } =
      .ok (Cache.raw.codes[68]!, { bytes := artifactBytes, pos := 8640, limit := 21767 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 8612, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 8615, limit := 8640 })
    (bodyFinish := { bytes := artifactBytes, pos := 8640, limit := 8640 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code68_tail0_decoded
  · rfl

#print axioms code68_decoded

@[cbv_eval] theorem code69_tail0_decoded :
    instructionSequenceAt 145 false { bytes := artifactBytes, pos := 8645, limit := 8790 } =
      .ok (((Cache.raw.codes[69]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 8790, limit := 8790 }) := by
  cbv

theorem code69_decoded :
    code { bytes := artifactBytes, pos := 8640, limit := 21767 } =
      .ok (Cache.raw.codes[69]!, { bytes := artifactBytes, pos := 8790, limit := 21767 }) := by
  refine code_eq_of_parts (size := 148)
    (payload := { bytes := artifactBytes, pos := 8642, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 8645, limit := 8790 })
    (bodyFinish := { bytes := artifactBytes, pos := 8790, limit := 8790 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code69_tail0_decoded
  · rfl

#print axioms code69_decoded

@[cbv_eval] theorem code70_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 8794, limit := 8801 } =
      .ok (((Cache.raw.codes[70]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 8801, limit := 8801 }) := by
  cbv

theorem code70_decoded :
    code { bytes := artifactBytes, pos := 8790, limit := 21767 } =
      .ok (Cache.raw.codes[70]!, { bytes := artifactBytes, pos := 8801, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 8791, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 8794, limit := 8801 })
    (bodyFinish := { bytes := artifactBytes, pos := 8801, limit := 8801 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code70_tail0_decoded
  · rfl

#print axioms code70_decoded

@[cbv_eval] theorem code71_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 8805, limit := 8812 } =
      .ok (((Cache.raw.codes[71]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 8812, limit := 8812 }) := by
  cbv

theorem code71_decoded :
    code { bytes := artifactBytes, pos := 8801, limit := 21767 } =
      .ok (Cache.raw.codes[71]!, { bytes := artifactBytes, pos := 8812, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 8802, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 8805, limit := 8812 })
    (bodyFinish := { bytes := artifactBytes, pos := 8812, limit := 8812 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code71_tail0_decoded
  · rfl

#print axioms code71_decoded

@[cbv_eval] theorem code72_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 8816, limit := 8823 } =
      .ok (((Cache.raw.codes[72]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 8823, limit := 8823 }) := by
  cbv

theorem code72_decoded :
    code { bytes := artifactBytes, pos := 8812, limit := 21767 } =
      .ok (Cache.raw.codes[72]!, { bytes := artifactBytes, pos := 8823, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 8813, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 8816, limit := 8823 })
    (bodyFinish := { bytes := artifactBytes, pos := 8823, limit := 8823 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code72_tail0_decoded
  · rfl

#print axioms code72_decoded

@[cbv_eval] theorem code73_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 8827, limit := 8834 } =
      .ok (((Cache.raw.codes[73]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 8834, limit := 8834 }) := by
  cbv

theorem code73_decoded :
    code { bytes := artifactBytes, pos := 8823, limit := 21767 } =
      .ok (Cache.raw.codes[73]!, { bytes := artifactBytes, pos := 8834, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 8824, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 8827, limit := 8834 })
    (bodyFinish := { bytes := artifactBytes, pos := 8834, limit := 8834 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code73_tail0_decoded
  · rfl

#print axioms code73_decoded

@[cbv_eval] theorem code74_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 8838, limit := 8845 } =
      .ok (((Cache.raw.codes[74]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 8845, limit := 8845 }) := by
  cbv

theorem code74_decoded :
    code { bytes := artifactBytes, pos := 8834, limit := 21767 } =
      .ok (Cache.raw.codes[74]!, { bytes := artifactBytes, pos := 8845, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 8835, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 8838, limit := 8845 })
    (bodyFinish := { bytes := artifactBytes, pos := 8845, limit := 8845 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code74_tail0_decoded
  · rfl

#print axioms code74_decoded

@[cbv_eval] theorem code75_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 8849, limit := 8856 } =
      .ok (((Cache.raw.codes[75]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 8856, limit := 8856 }) := by
  cbv

theorem code75_decoded :
    code { bytes := artifactBytes, pos := 8845, limit := 21767 } =
      .ok (Cache.raw.codes[75]!, { bytes := artifactBytes, pos := 8856, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 8846, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 8849, limit := 8856 })
    (bodyFinish := { bytes := artifactBytes, pos := 8856, limit := 8856 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code75_tail0_decoded
  · rfl

#print axioms code75_decoded

@[cbv_eval] theorem code76_tail51_decoded :
    instructionSequenceAt 308 false { bytes := artifactBytes, pos := 8963, limit := 9220 } =
      .ok (((Cache.raw.codes[76]!).body.drop 51, .end),
        { bytes := artifactBytes, pos := 9220, limit := 9220 }) := by
  cbv

@[cbv_eval] theorem code76_tail0_decoded :
    instructionSequenceAt 359 false { bytes := artifactBytes, pos := 8861, limit := 9220 } =
      .ok (((Cache.raw.codes[76]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 9220, limit := 9220 }) := by
  cbv

theorem code76_decoded :
    code { bytes := artifactBytes, pos := 8856, limit := 21767 } =
      .ok (Cache.raw.codes[76]!, { bytes := artifactBytes, pos := 9220, limit := 21767 }) := by
  refine code_eq_of_parts (size := 362)
    (payload := { bytes := artifactBytes, pos := 8858, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 8861, limit := 9220 })
    (bodyFinish := { bytes := artifactBytes, pos := 9220, limit := 9220 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code76_tail0_decoded
  · rfl

#print axioms code76_decoded

@[cbv_eval] theorem code78_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 10060, limit := 10067 } =
      .ok (((Cache.raw.codes[78]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 10067, limit := 10067 }) := by
  cbv

theorem code78_decoded :
    code { bytes := artifactBytes, pos := 10056, limit := 21767 } =
      .ok (Cache.raw.codes[78]!, { bytes := artifactBytes, pos := 10067, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 10057, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 10060, limit := 10067 })
    (bodyFinish := { bytes := artifactBytes, pos := 10067, limit := 10067 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code78_tail0_decoded
  · rfl

#print axioms code78_decoded

@[cbv_eval] theorem code79_tail0_decoded :
    instructionSequenceAt 242 false { bytes := artifactBytes, pos := 10072, limit := 10314 } =
      .ok (((Cache.raw.codes[79]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 10314, limit := 10314 }) := by
  cbv

theorem code79_decoded :
    code { bytes := artifactBytes, pos := 10067, limit := 21767 } =
      .ok (Cache.raw.codes[79]!, { bytes := artifactBytes, pos := 10314, limit := 21767 }) := by
  refine code_eq_of_parts (size := 245)
    (payload := { bytes := artifactBytes, pos := 10069, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 10072, limit := 10314 })
    (bodyFinish := { bytes := artifactBytes, pos := 10314, limit := 10314 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code79_tail0_decoded
  · rfl

#print axioms code79_decoded

@[cbv_eval] theorem code80_tail0_decoded :
    instructionSequenceAt 154 false { bytes := artifactBytes, pos := 10319, limit := 10473 } =
      .ok (((Cache.raw.codes[80]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 10473, limit := 10473 }) := by
  cbv

theorem code80_decoded :
    code { bytes := artifactBytes, pos := 10314, limit := 21767 } =
      .ok (Cache.raw.codes[80]!, { bytes := artifactBytes, pos := 10473, limit := 21767 }) := by
  refine code_eq_of_parts (size := 157)
    (payload := { bytes := artifactBytes, pos := 10316, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 10319, limit := 10473 })
    (bodyFinish := { bytes := artifactBytes, pos := 10473, limit := 10473 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code80_tail0_decoded
  · rfl

#print axioms code80_decoded

@[cbv_eval] theorem code82_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 11610, limit := 11617 } =
      .ok (((Cache.raw.codes[82]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 11617, limit := 11617 }) := by
  cbv

theorem code82_decoded :
    code { bytes := artifactBytes, pos := 11606, limit := 21767 } =
      .ok (Cache.raw.codes[82]!, { bytes := artifactBytes, pos := 11617, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 11607, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 11610, limit := 11617 })
    (bodyFinish := { bytes := artifactBytes, pos := 11617, limit := 11617 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code82_tail0_decoded
  · rfl

#print axioms code82_decoded

end Project.EulerRiemann.Artifact
