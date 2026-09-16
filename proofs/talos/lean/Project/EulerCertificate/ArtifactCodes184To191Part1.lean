import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes184To191Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code184_decoded :
    code { bytes := artifactBytes, pos := 41455, limit := 45644 } =
      .ok (Cache.raw.codes[184]!, { bytes := artifactBytes, pos := 42734, limit := 45644 }) := by
  refine code_eq_of_parts (size := 1277)
    (payload := { bytes := artifactBytes, pos := 41457, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 41461, limit := 42734 })
    (bodyFinish := { bytes := artifactBytes, pos := 42734, limit := 42734 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code184_seq_184_tail0_decoded
  · rfl

#print axioms code184_decoded

@[cbv_eval] theorem code185_seq_185_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 42738, limit := 42751 } =
      .ok ((((Cache.raw.codes[185]!).body).drop 0, .end), { bytes := artifactBytes, pos := 42751, limit := 42751 }) := by
  cbv

theorem code185_decoded :
    code { bytes := artifactBytes, pos := 42734, limit := 45644 } =
      .ok (Cache.raw.codes[185]!, { bytes := artifactBytes, pos := 42751, limit := 45644 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 42735, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 42738, limit := 42751 })
    (bodyFinish := { bytes := artifactBytes, pos := 42751, limit := 42751 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code185_seq_185_tail0_decoded
  · rfl

#print axioms code185_decoded

@[cbv_eval] theorem code186_seq_186_tail0_decoded :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 42755, limit := 42828 } =
      .ok ((((Cache.raw.codes[186]!).body).drop 0, .end), { bytes := artifactBytes, pos := 42828, limit := 42828 }) := by
  cbv

theorem code186_decoded :
    code { bytes := artifactBytes, pos := 42751, limit := 45644 } =
      .ok (Cache.raw.codes[186]!, { bytes := artifactBytes, pos := 42828, limit := 45644 }) := by
  refine code_eq_of_parts (size := 76)
    (payload := { bytes := artifactBytes, pos := 42752, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 42755, limit := 42828 })
    (bodyFinish := { bytes := artifactBytes, pos := 42828, limit := 42828 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code186_seq_186_tail0_decoded
  · rfl

#print axioms code186_decoded

@[cbv_eval] theorem code187_seq_187_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 42832, limit := 42839 } =
      .ok ((((Cache.raw.codes[187]!).body).drop 0, .end), { bytes := artifactBytes, pos := 42839, limit := 42839 }) := by
  cbv

theorem code187_decoded :
    code { bytes := artifactBytes, pos := 42828, limit := 45644 } =
      .ok (Cache.raw.codes[187]!, { bytes := artifactBytes, pos := 42839, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 42829, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 42832, limit := 42839 })
    (bodyFinish := { bytes := artifactBytes, pos := 42839, limit := 42839 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code187_seq_187_tail0_decoded
  · rfl

#print axioms code187_decoded

@[cbv_eval] theorem code188_seq_188_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 42843, limit := 42850 } =
      .ok ((((Cache.raw.codes[188]!).body).drop 0, .end), { bytes := artifactBytes, pos := 42850, limit := 42850 }) := by
  cbv

theorem code188_decoded :
    code { bytes := artifactBytes, pos := 42839, limit := 45644 } =
      .ok (Cache.raw.codes[188]!, { bytes := artifactBytes, pos := 42850, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 42840, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 42843, limit := 42850 })
    (bodyFinish := { bytes := artifactBytes, pos := 42850, limit := 42850 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code188_seq_188_tail0_decoded
  · rfl

#print axioms code188_decoded

@[cbv_eval] theorem code189_seq_189_4_e_38_t_0_t_tail23_decoded :
    instructionSequenceAt 1719 false { bytes := artifactBytes, pos := 44187, limit := 44646 } =
      .ok ((((((((((Cache.raw.codes[189]!).body)[4]!).childBody true)[38]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := artifactBytes, pos := 44322, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_e_38_t_0_t_tail0_decoded :
    instructionSequenceAt 1742 false { bytes := artifactBytes, pos := 44138, limit := 44646 } =
      .ok ((((((((((Cache.raw.codes[189]!).body)[4]!).childBody true)[38]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 44322, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_e_38_t_tail0_decoded :
    instructionSequenceAt 1744 false { bytes := artifactBytes, pos := 44136, limit := 44646 } =
      .ok ((((((((Cache.raw.codes[189]!).body)[4]!).childBody true)[38]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 44323, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_e_42_t_tail14_decoded :
    instructionSequenceAt 1726 true { bytes := artifactBytes, pos := 44361, limit := 44646 } =
      .ok ((((((((Cache.raw.codes[189]!).body)[4]!).childBody true)[42]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 44490, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_e_42_t_tail0_decoded :
    instructionSequenceAt 1740 true { bytes := artifactBytes, pos := 44331, limit := 44646 } =
      .ok ((((((((Cache.raw.codes[189]!).body)[4]!).childBody true)[42]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 44490, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_t_tail434_decoded :
    instructionSequenceAt 1350 true { bytes := artifactBytes, pos := 43914, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody false).drop 434, .otherwise), { bytes := artifactBytes, pos := 44043, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_t_tail391_decoded :
    instructionSequenceAt 1393 true { bytes := artifactBytes, pos := 43785, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody false).drop 391, .otherwise), { bytes := artifactBytes, pos := 44043, limit := 44646 }) := by
  cbv

end Project.EulerCertificate.Artifact
