import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code144_seq_144_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 29854, limit := 29879 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 0, .end), { bytes := artifactBytes, pos := 29879, limit := 29879 }) := by
  cbv

theorem code144_decoded :
    code { bytes := artifactBytes, pos := 29850, limit := 45644 } =
      .ok (Cache.raw.codes[144]!, { bytes := artifactBytes, pos := 29879, limit := 45644 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 29851, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 29854, limit := 29879 })
    (bodyFinish := { bytes := artifactBytes, pos := 29879, limit := 29879 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code144_seq_144_tail0_decoded
  · rfl

#print axioms code144_decoded

@[cbv_eval] theorem code145_seq_145_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 29883, limit := 29908 } =
      .ok ((((Cache.raw.codes[145]!).body).drop 0, .end), { bytes := artifactBytes, pos := 29908, limit := 29908 }) := by
  cbv

theorem code145_decoded :
    code { bytes := artifactBytes, pos := 29879, limit := 45644 } =
      .ok (Cache.raw.codes[145]!, { bytes := artifactBytes, pos := 29908, limit := 45644 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 29880, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 29883, limit := 29908 })
    (bodyFinish := { bytes := artifactBytes, pos := 29908, limit := 29908 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code145_seq_145_tail0_decoded
  · rfl

#print axioms code145_decoded

@[cbv_eval] theorem code146_seq_146_204_t_tail44_decoded :
    instructionSequenceAt 545 true { bytes := artifactBytes, pos := 30480, limit := 30709 } =
      .ok ((((((Cache.raw.codes[146]!).body)[204]!).childBody false).drop 44, .otherwise), { bytes := artifactBytes, pos := 30608, limit := 30709 }) := by
  cbv

@[cbv_eval] theorem code146_seq_146_204_t_tail0_decoded :
    instructionSequenceAt 589 true { bytes := artifactBytes, pos := 30378, limit := 30709 } =
      .ok ((((((Cache.raw.codes[146]!).body)[204]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 30608, limit := 30709 }) := by
  cbv

@[cbv_eval] theorem code146_seq_146_tail204_decoded :
    instructionSequenceAt 591 false { bytes := artifactBytes, pos := 30376, limit := 30709 } =
      .ok ((((Cache.raw.codes[146]!).body).drop 204, .end), { bytes := artifactBytes, pos := 30709, limit := 30709 }) := by
  cbv

@[cbv_eval] theorem code146_seq_146_tail167_decoded :
    instructionSequenceAt 628 false { bytes := artifactBytes, pos := 30248, limit := 30709 } =
      .ok ((((Cache.raw.codes[146]!).body).drop 167, .end), { bytes := artifactBytes, pos := 30709, limit := 30709 }) := by
  cbv

@[cbv_eval] theorem code146_seq_146_tail103_decoded :
    instructionSequenceAt 692 false { bytes := artifactBytes, pos := 30120, limit := 30709 } =
      .ok ((((Cache.raw.codes[146]!).body).drop 103, .end), { bytes := artifactBytes, pos := 30709, limit := 30709 }) := by
  cbv

@[cbv_eval] theorem code146_seq_146_tail39_decoded :
    instructionSequenceAt 756 false { bytes := artifactBytes, pos := 29992, limit := 30709 } =
      .ok ((((Cache.raw.codes[146]!).body).drop 39, .end), { bytes := artifactBytes, pos := 30709, limit := 30709 }) := by
  cbv

@[cbv_eval] theorem code146_seq_146_tail0_decoded :
    instructionSequenceAt 795 false { bytes := artifactBytes, pos := 29914, limit := 30709 } =
      .ok ((((Cache.raw.codes[146]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30709, limit := 30709 }) := by
  cbv

theorem code146_decoded :
    code { bytes := artifactBytes, pos := 29908, limit := 45644 } =
      .ok (Cache.raw.codes[146]!, { bytes := artifactBytes, pos := 30709, limit := 45644 }) := by
  refine code_eq_of_parts (size := 799)
    (payload := { bytes := artifactBytes, pos := 29910, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 29914, limit := 30709 })
    (bodyFinish := { bytes := artifactBytes, pos := 30709, limit := 30709 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code146_seq_146_tail0_decoded
  · rfl

#print axioms code146_decoded

@[cbv_eval] theorem code147_seq_147_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 30713, limit := 30738 } =
      .ok ((((Cache.raw.codes[147]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30738, limit := 30738 }) := by
  cbv

theorem code147_decoded :
    code { bytes := artifactBytes, pos := 30709, limit := 45644 } =
      .ok (Cache.raw.codes[147]!, { bytes := artifactBytes, pos := 30738, limit := 45644 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 30710, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 30713, limit := 30738 })
    (bodyFinish := { bytes := artifactBytes, pos := 30738, limit := 30738 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code147_seq_147_tail0_decoded
  · rfl

#print axioms code147_decoded

@[cbv_eval] theorem code148_seq_148_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 30742, limit := 30767 } =
      .ok ((((Cache.raw.codes[148]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30767, limit := 30767 }) := by
  cbv

theorem code148_decoded :
    code { bytes := artifactBytes, pos := 30738, limit := 45644 } =
      .ok (Cache.raw.codes[148]!, { bytes := artifactBytes, pos := 30767, limit := 45644 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 30739, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 30742, limit := 30767 })
    (bodyFinish := { bytes := artifactBytes, pos := 30767, limit := 30767 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code148_seq_148_tail0_decoded
  · rfl

#print axioms code148_decoded

end Project.EulerCertificate.Artifact
