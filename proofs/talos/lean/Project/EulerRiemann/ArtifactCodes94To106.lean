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

@[cbv_eval] theorem code94_tail63_decoded :
    instructionSequenceAt 554 false { bytes := artifactBytes, pos := 13621, limit := 13877 } =
      .ok (((Cache.raw.codes[94]!).body.drop 63, .end),
        { bytes := artifactBytes, pos := 13877, limit := 13877 }) := by
  cbv

@[cbv_eval] theorem code94_tail27_decoded :
    instructionSequenceAt 590 false { bytes := artifactBytes, pos := 13364, limit := 13877 } =
      .ok (((Cache.raw.codes[94]!).body.drop 27, .end),
        { bytes := artifactBytes, pos := 13877, limit := 13877 }) := by
  cbv

@[cbv_eval] theorem code94_tail0_decoded :
    instructionSequenceAt 617 false { bytes := artifactBytes, pos := 13260, limit := 13877 } =
      .ok (((Cache.raw.codes[94]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 13877, limit := 13877 }) := by
  cbv

theorem code94_decoded :
    code { bytes := artifactBytes, pos := 13255, limit := 21767 } =
      .ok (Cache.raw.codes[94]!, { bytes := artifactBytes, pos := 13877, limit := 21767 }) := by
  refine code_eq_of_parts (size := 620)
    (payload := { bytes := artifactBytes, pos := 13257, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 13260, limit := 13877 })
    (bodyFinish := { bytes := artifactBytes, pos := 13877, limit := 13877 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code94_tail0_decoded
  · rfl

#print axioms code94_decoded

@[cbv_eval] theorem code98_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 18027, limit := 18034 } =
      .ok (((Cache.raw.codes[98]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 18034, limit := 18034 }) := by
  cbv

theorem code98_decoded :
    code { bytes := artifactBytes, pos := 18023, limit := 21767 } =
      .ok (Cache.raw.codes[98]!, { bytes := artifactBytes, pos := 18034, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 18024, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 18027, limit := 18034 })
    (bodyFinish := { bytes := artifactBytes, pos := 18034, limit := 18034 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code98_tail0_decoded
  · rfl

#print axioms code98_decoded

@[cbv_eval] theorem code100_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 20824, limit := 20831 } =
      .ok (((Cache.raw.codes[100]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 20831, limit := 20831 }) := by
  cbv

theorem code100_decoded :
    code { bytes := artifactBytes, pos := 20820, limit := 21767 } =
      .ok (Cache.raw.codes[100]!, { bytes := artifactBytes, pos := 20831, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 20821, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 20824, limit := 20831 })
    (bodyFinish := { bytes := artifactBytes, pos := 20831, limit := 20831 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code100_tail0_decoded
  · rfl

#print axioms code100_decoded

@[cbv_eval] theorem code101_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 20835, limit := 20842 } =
      .ok (((Cache.raw.codes[101]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 20842, limit := 20842 }) := by
  cbv

theorem code101_decoded :
    code { bytes := artifactBytes, pos := 20831, limit := 21767 } =
      .ok (Cache.raw.codes[101]!, { bytes := artifactBytes, pos := 20842, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 20832, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 20835, limit := 20842 })
    (bodyFinish := { bytes := artifactBytes, pos := 20842, limit := 20842 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code101_tail0_decoded
  · rfl

#print axioms code101_decoded

@[cbv_eval] theorem code102_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 20846, limit := 20859 } =
      .ok (((Cache.raw.codes[102]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 20859, limit := 20859 }) := by
  cbv

theorem code102_decoded :
    code { bytes := artifactBytes, pos := 20842, limit := 21767 } =
      .ok (Cache.raw.codes[102]!, { bytes := artifactBytes, pos := 20859, limit := 21767 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 20843, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 20846, limit := 20859 })
    (bodyFinish := { bytes := artifactBytes, pos := 20859, limit := 20859 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code102_tail0_decoded
  · rfl

#print axioms code102_decoded

@[cbv_eval] theorem code103_tail0_decoded :
    instructionSequenceAt 75 false { bytes := artifactBytes, pos := 20863, limit := 20938 } =
      .ok (((Cache.raw.codes[103]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 20938, limit := 20938 }) := by
  cbv

theorem code103_decoded :
    code { bytes := artifactBytes, pos := 20859, limit := 21767 } =
      .ok (Cache.raw.codes[103]!, { bytes := artifactBytes, pos := 20938, limit := 21767 }) := by
  refine code_eq_of_parts (size := 78)
    (payload := { bytes := artifactBytes, pos := 20860, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 20863, limit := 20938 })
    (bodyFinish := { bytes := artifactBytes, pos := 20938, limit := 20938 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code103_tail0_decoded
  · rfl

#print axioms code103_decoded

@[cbv_eval] theorem code104_tail18_decoded :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 20980, limit := 21305 } =
      .ok (((Cache.raw.codes[104]!).body.drop 18, .end),
        { bytes := artifactBytes, pos := 21305, limit := 21305 }) := by
  cbv

@[cbv_eval] theorem code104_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 20943, limit := 21305 } =
      .ok (((Cache.raw.codes[104]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 21305, limit := 21305 }) := by
  cbv

theorem code104_decoded :
    code { bytes := artifactBytes, pos := 20938, limit := 21767 } =
      .ok (Cache.raw.codes[104]!, { bytes := artifactBytes, pos := 21305, limit := 21767 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 20940, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 20943, limit := 21305 })
    (bodyFinish := { bytes := artifactBytes, pos := 21305, limit := 21305 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code104_tail0_decoded
  · rfl

#print axioms code104_decoded

@[cbv_eval] theorem code105_tail0_decoded :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 21307, limit := 21333 } =
      .ok (((Cache.raw.codes[105]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 21333, limit := 21333 }) := by
  cbv

theorem code105_decoded :
    code { bytes := artifactBytes, pos := 21305, limit := 21767 } =
      .ok (Cache.raw.codes[105]!, { bytes := artifactBytes, pos := 21333, limit := 21767 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 21306, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 21307, limit := 21333 })
    (bodyFinish := { bytes := artifactBytes, pos := 21333, limit := 21333 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code105_tail0_decoded
  · rfl

#print axioms code105_decoded

@[cbv_eval] theorem code106_tail0_decoded :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 21337, limit := 21414 } =
      .ok (((Cache.raw.codes[106]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 21414, limit := 21414 }) := by
  cbv

theorem code106_decoded :
    code { bytes := artifactBytes, pos := 21333, limit := 21767 } =
      .ok (Cache.raw.codes[106]!, { bytes := artifactBytes, pos := 21414, limit := 21767 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 21334, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 21337, limit := 21414 })
    (bodyFinish := { bytes := artifactBytes, pos := 21414, limit := 21414 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code106_tail0_decoded
  · rfl

#print axioms code106_decoded

end Project.EulerRiemann.Artifact
