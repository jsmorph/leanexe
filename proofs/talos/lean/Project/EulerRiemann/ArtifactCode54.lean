import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactByteLookup
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code54_seq_54_43_t_43_t_tail53_decoded :
    instructionSequenceAt 508 true { bytes := artifactBytes, pos := 6608, limit := 6956 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[43]!).childBody false)[43]!).childBody false).drop 53, .otherwise), { bytes := artifactBytes, pos := 6864, limit := 6956 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_43_t_tail0_decoded :
    instructionSequenceAt 561 true { bytes := artifactBytes, pos := 6497, limit := 6956 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[43]!).childBody false)[43]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 6864, limit := 6956 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_tail43_decoded :
    instructionSequenceAt 563 true { bytes := artifactBytes, pos := 6495, limit := 6956 } =
      .ok ((((((Cache.raw.codes[54]!).body)[43]!).childBody false).drop 43, .otherwise), { bytes := artifactBytes, pos := 6904, limit := 6956 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_tail0_decoded :
    instructionSequenceAt 606 true { bytes := artifactBytes, pos := 6401, limit := 6956 } =
      .ok ((((((Cache.raw.codes[54]!).body)[43]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 6904, limit := 6956 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_tail43_decoded :
    instructionSequenceAt 608 false { bytes := artifactBytes, pos := 6399, limit := 6956 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 43, .end), { bytes := artifactBytes, pos := 6956, limit := 6956 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_tail0_decoded :
    instructionSequenceAt 651 false { bytes := artifactBytes, pos := 6305, limit := 6956 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6956, limit := 6956 }) := by
  cbv

theorem code54_decoded :
    code { bytes := artifactBytes, pos := 6300, limit := 21767 } =
      .ok (Cache.raw.codes[54]!, { bytes := artifactBytes, pos := 6956, limit := 21767 }) := by
  refine code_eq_of_parts (size := 654)
    (payload := { bytes := artifactBytes, pos := 6302, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 6305, limit := 6956 })
    (bodyFinish := { bytes := artifactBytes, pos := 6956, limit := 6956 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code54_seq_54_tail0_decoded
  · rfl

#print axioms code54_decoded

end Project.EulerRiemann.Artifact
