import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code56_seq_56_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6575, limit := 6582 } =
      .ok ((((Cache.raw.codes[56]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6582, limit := 6582 }) := by
  cbv

theorem code56_decoded :
    code { bytes := artifactBytes, pos := 6571, limit := 9077 } =
      .ok (Cache.raw.codes[56]!, { bytes := artifactBytes, pos := 6582, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6572, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6575, limit := 6582 })
    (bodyFinish := { bytes := artifactBytes, pos := 6582, limit := 6582 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code56_seq_56_tail0_decoded
  · rfl

#print axioms code56_decoded

@[cbv_eval] theorem code57_seq_57_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6586, limit := 6593 } =
      .ok ((((Cache.raw.codes[57]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6593, limit := 6593 }) := by
  cbv

theorem code57_decoded :
    code { bytes := artifactBytes, pos := 6582, limit := 9077 } =
      .ok (Cache.raw.codes[57]!, { bytes := artifactBytes, pos := 6593, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6583, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6586, limit := 6593 })
    (bodyFinish := { bytes := artifactBytes, pos := 6593, limit := 6593 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code57_seq_57_tail0_decoded
  · rfl

#print axioms code57_decoded

@[cbv_eval] theorem code58_seq_58_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6597, limit := 6604 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6604, limit := 6604 }) := by
  cbv

theorem code58_decoded :
    code { bytes := artifactBytes, pos := 6593, limit := 9077 } =
      .ok (Cache.raw.codes[58]!, { bytes := artifactBytes, pos := 6604, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6594, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6597, limit := 6604 })
    (bodyFinish := { bytes := artifactBytes, pos := 6604, limit := 6604 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code58_seq_58_tail0_decoded
  · rfl

#print axioms code58_decoded

@[cbv_eval] theorem code59_seq_59_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6608, limit := 6615 } =
      .ok ((((Cache.raw.codes[59]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6615, limit := 6615 }) := by
  cbv

theorem code59_decoded :
    code { bytes := artifactBytes, pos := 6604, limit := 9077 } =
      .ok (Cache.raw.codes[59]!, { bytes := artifactBytes, pos := 6615, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6605, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6608, limit := 6615 })
    (bodyFinish := { bytes := artifactBytes, pos := 6615, limit := 6615 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code59_seq_59_tail0_decoded
  · rfl

#print axioms code59_decoded

@[cbv_eval] theorem code60_seq_60_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6619, limit := 6626 } =
      .ok ((((Cache.raw.codes[60]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6626, limit := 6626 }) := by
  cbv

theorem code60_decoded :
    code { bytes := artifactBytes, pos := 6615, limit := 9077 } =
      .ok (Cache.raw.codes[60]!, { bytes := artifactBytes, pos := 6626, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6616, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6619, limit := 6626 })
    (bodyFinish := { bytes := artifactBytes, pos := 6626, limit := 6626 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code60_seq_60_tail0_decoded
  · rfl

#print axioms code60_decoded

@[cbv_eval] theorem code61_seq_61_tail18_decoded :
    instructionSequenceAt 221 false { bytes := artifactBytes, pos := 6865, limit := 6870 } =
      .ok ((((Cache.raw.codes[61]!).body).drop 18, .end), { bytes := artifactBytes, pos := 6870, limit := 6870 }) := by
  cbv

@[cbv_eval] theorem code61_seq_61_tail17_decoded :
    instructionSequenceAt 222 false { bytes := artifactBytes, pos := 6720, limit := 6870 } =
      .ok ((((Cache.raw.codes[61]!).body).drop 17, .end), { bytes := artifactBytes, pos := 6870, limit := 6870 }) := by
  cbv

@[cbv_eval] theorem code61_seq_61_tail0_decoded :
    instructionSequenceAt 239 false { bytes := artifactBytes, pos := 6631, limit := 6870 } =
      .ok ((((Cache.raw.codes[61]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6870, limit := 6870 }) := by
  cbv

theorem code61_decoded :
    code { bytes := artifactBytes, pos := 6626, limit := 9077 } =
      .ok (Cache.raw.codes[61]!, { bytes := artifactBytes, pos := 6870, limit := 9077 }) := by
  refine code_eq_of_parts (size := 242)
    (payload := { bytes := artifactBytes, pos := 6628, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6631, limit := 6870 })
    (bodyFinish := { bytes := artifactBytes, pos := 6870, limit := 6870 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code61_seq_61_tail0_decoded
  · rfl

#print axioms code61_decoded

@[cbv_eval] theorem code62_seq_62_tail0_decoded :
    instructionSequenceAt 43 false { bytes := artifactBytes, pos := 6874, limit := 6917 } =
      .ok ((((Cache.raw.codes[62]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6917, limit := 6917 }) := by
  cbv

theorem code62_decoded :
    code { bytes := artifactBytes, pos := 6870, limit := 9077 } =
      .ok (Cache.raw.codes[62]!, { bytes := artifactBytes, pos := 6917, limit := 9077 }) := by
  refine code_eq_of_parts (size := 46)
    (payload := { bytes := artifactBytes, pos := 6871, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6874, limit := 6917 })
    (bodyFinish := { bytes := artifactBytes, pos := 6917, limit := 6917 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code62_seq_62_tail0_decoded
  · rfl

#print axioms code62_decoded

@[cbv_eval] theorem code63_seq_63_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6921, limit := 6928 } =
      .ok ((((Cache.raw.codes[63]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6928, limit := 6928 }) := by
  cbv

theorem code63_decoded :
    code { bytes := artifactBytes, pos := 6917, limit := 9077 } =
      .ok (Cache.raw.codes[63]!, { bytes := artifactBytes, pos := 6928, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6918, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6921, limit := 6928 })
    (bodyFinish := { bytes := artifactBytes, pos := 6928, limit := 6928 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code63_seq_63_tail0_decoded
  · rfl

#print axioms code63_decoded


end Project.EulerOutwardFaceStep.Artifact
