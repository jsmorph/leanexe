import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes72To79Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code75_seq_75_tail102_decoded :
    instructionSequenceAt 231 false { bytes := artifactBytes, pos := 18657, limit := 18786 } =
      .ok ((((Cache.raw.codes[75]!).body).drop 102, .end), { bytes := artifactBytes, pos := 18786, limit := 18786 }) := by
  cbv

@[cbv_eval] theorem code75_seq_75_tail38_decoded :
    instructionSequenceAt 295 false { bytes := artifactBytes, pos := 18529, limit := 18786 } =
      .ok ((((Cache.raw.codes[75]!).body).drop 38, .end), { bytes := artifactBytes, pos := 18786, limit := 18786 }) := by
  cbv

@[cbv_eval] theorem code75_seq_75_tail0_decoded :
    instructionSequenceAt 333 false { bytes := artifactBytes, pos := 18453, limit := 18786 } =
      .ok ((((Cache.raw.codes[75]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18786, limit := 18786 }) := by
  cbv

theorem code75_decoded :
    code { bytes := artifactBytes, pos := 18448, limit := 45644 } =
      .ok (Cache.raw.codes[75]!, { bytes := artifactBytes, pos := 18786, limit := 45644 }) := by
  refine code_eq_of_parts (size := 336)
    (payload := { bytes := artifactBytes, pos := 18450, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 18453, limit := 18786 })
    (bodyFinish := { bytes := artifactBytes, pos := 18786, limit := 18786 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code75_seq_75_tail0_decoded
  · rfl

#print axioms code75_decoded

@[cbv_eval] theorem code76_seq_76_tail0_decoded :
    instructionSequenceAt 15 false { bytes := artifactBytes, pos := 18790, limit := 18805 } =
      .ok ((((Cache.raw.codes[76]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18805, limit := 18805 }) := by
  cbv

theorem code76_decoded :
    code { bytes := artifactBytes, pos := 18786, limit := 45644 } =
      .ok (Cache.raw.codes[76]!, { bytes := artifactBytes, pos := 18805, limit := 45644 }) := by
  refine code_eq_of_parts (size := 18)
    (payload := { bytes := artifactBytes, pos := 18787, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 18790, limit := 18805 })
    (bodyFinish := { bytes := artifactBytes, pos := 18805, limit := 18805 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code76_seq_76_tail0_decoded
  · rfl

#print axioms code76_decoded

@[cbv_eval] theorem code77_seq_77_tail0_decoded :
    instructionSequenceAt 105 false { bytes := artifactBytes, pos := 18809, limit := 18914 } =
      .ok ((((Cache.raw.codes[77]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18914, limit := 18914 }) := by
  cbv

theorem code77_decoded :
    code { bytes := artifactBytes, pos := 18805, limit := 45644 } =
      .ok (Cache.raw.codes[77]!, { bytes := artifactBytes, pos := 18914, limit := 45644 }) := by
  refine code_eq_of_parts (size := 108)
    (payload := { bytes := artifactBytes, pos := 18806, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 18809, limit := 18914 })
    (bodyFinish := { bytes := artifactBytes, pos := 18914, limit := 18914 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code77_seq_77_tail0_decoded
  · rfl

#print axioms code77_decoded

@[cbv_eval] theorem code78_seq_78_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 18918, limit := 19026 } =
      .ok ((((Cache.raw.codes[78]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19026, limit := 19026 }) := by
  cbv

theorem code78_decoded :
    code { bytes := artifactBytes, pos := 18914, limit := 45644 } =
      .ok (Cache.raw.codes[78]!, { bytes := artifactBytes, pos := 19026, limit := 45644 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 18915, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 18918, limit := 19026 })
    (bodyFinish := { bytes := artifactBytes, pos := 19026, limit := 19026 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code78_seq_78_tail0_decoded
  · rfl

#print axioms code78_decoded

@[cbv_eval] theorem code79_seq_79_47_t_tail26_decoded :
    instructionSequenceAt 271 true { bytes := artifactBytes, pos := 19220, limit := 19377 } =
      .ok ((((((Cache.raw.codes[79]!).body)[47]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 19357, limit := 19377 }) := by
  cbv

@[cbv_eval] theorem code79_seq_79_47_t_tail0_decoded :
    instructionSequenceAt 297 true { bytes := artifactBytes, pos := 19160, limit := 19377 } =
      .ok ((((((Cache.raw.codes[79]!).body)[47]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 19357, limit := 19377 }) := by
  cbv

@[cbv_eval] theorem code79_seq_79_tail47_decoded :
    instructionSequenceAt 299 false { bytes := artifactBytes, pos := 19158, limit := 19377 } =
      .ok ((((Cache.raw.codes[79]!).body).drop 47, .end), { bytes := artifactBytes, pos := 19377, limit := 19377 }) := by
  cbv

@[cbv_eval] theorem code79_seq_79_tail0_decoded :
    instructionSequenceAt 346 false { bytes := artifactBytes, pos := 19031, limit := 19377 } =
      .ok ((((Cache.raw.codes[79]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19377, limit := 19377 }) := by
  cbv

theorem code79_decoded :
    code { bytes := artifactBytes, pos := 19026, limit := 45644 } =
      .ok (Cache.raw.codes[79]!, { bytes := artifactBytes, pos := 19377, limit := 45644 }) := by
  refine code_eq_of_parts (size := 349)
    (payload := { bytes := artifactBytes, pos := 19028, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 19031, limit := 19377 })
    (bodyFinish := { bytes := artifactBytes, pos := 19377, limit := 19377 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code79_seq_79_tail0_decoded
  · rfl

#print axioms code79_decoded

end Project.EulerCertificate.Artifact
