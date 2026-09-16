import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code96_seq_96_tail20_decoded :
    instructionSequenceAt 210 false { bytes := artifactBytes, pos := 21751, limit := 21879 } =
      .ok ((((Cache.raw.codes[96]!).body).drop 20, .end), { bytes := artifactBytes, pos := 21879, limit := 21879 }) := by
  cbv

@[cbv_eval] theorem code96_seq_96_tail0_decoded :
    instructionSequenceAt 230 false { bytes := artifactBytes, pos := 21649, limit := 21879 } =
      .ok ((((Cache.raw.codes[96]!).body).drop 0, .end), { bytes := artifactBytes, pos := 21879, limit := 21879 }) := by
  cbv

theorem code96_decoded :
    code { bytes := artifactBytes, pos := 21644, limit := 45644 } =
      .ok (Cache.raw.codes[96]!, { bytes := artifactBytes, pos := 21879, limit := 45644 }) := by
  refine code_eq_of_parts (size := 233)
    (payload := { bytes := artifactBytes, pos := 21646, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 21649, limit := 21879 })
    (bodyFinish := { bytes := artifactBytes, pos := 21879, limit := 21879 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code96_seq_96_tail0_decoded
  · rfl

#print axioms code96_decoded

@[cbv_eval] theorem code97_seq_97_tail0_decoded :
    instructionSequenceAt 62 false { bytes := artifactBytes, pos := 21883, limit := 21945 } =
      .ok ((((Cache.raw.codes[97]!).body).drop 0, .end), { bytes := artifactBytes, pos := 21945, limit := 21945 }) := by
  cbv

theorem code97_decoded :
    code { bytes := artifactBytes, pos := 21879, limit := 45644 } =
      .ok (Cache.raw.codes[97]!, { bytes := artifactBytes, pos := 21945, limit := 45644 }) := by
  refine code_eq_of_parts (size := 65)
    (payload := { bytes := artifactBytes, pos := 21880, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 21883, limit := 21945 })
    (bodyFinish := { bytes := artifactBytes, pos := 21945, limit := 21945 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code97_seq_97_tail0_decoded
  · rfl

#print axioms code97_decoded

@[cbv_eval] theorem code98_seq_98_71_t_tail10_decoded :
    instructionSequenceAt 1570 true { bytes := artifactBytes, pos := 22137, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[71]!).childBody false).drop 10, .otherwise), { bytes := artifactBytes, pos := 22266, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_71_t_tail0_decoded :
    instructionSequenceAt 1580 true { bytes := artifactBytes, pos := 22097, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[71]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 22266, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_71_e_tail10_decoded :
    instructionSequenceAt 1570 false { bytes := artifactBytes, pos := 22306, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[71]!).childBody true).drop 10, .end), { bytes := artifactBytes, pos := 22435, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_71_e_tail0_decoded :
    instructionSequenceAt 1580 false { bytes := artifactBytes, pos := 22266, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[71]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 22435, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_79_t_tail10_decoded :
    instructionSequenceAt 1562 true { bytes := artifactBytes, pos := 22494, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[79]!).childBody false).drop 10, .otherwise), { bytes := artifactBytes, pos := 22623, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_79_t_tail0_decoded :
    instructionSequenceAt 1572 true { bytes := artifactBytes, pos := 22454, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[79]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 22623, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_79_e_tail10_decoded :
    instructionSequenceAt 1562 false { bytes := artifactBytes, pos := 22663, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[79]!).childBody true).drop 10, .end), { bytes := artifactBytes, pos := 22792, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_79_e_tail0_decoded :
    instructionSequenceAt 1572 false { bytes := artifactBytes, pos := 22623, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[79]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 22792, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_115_t_tail10_decoded :
    instructionSequenceAt 1526 true { bytes := artifactBytes, pos := 22907, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[115]!).childBody false).drop 10, .otherwise), { bytes := artifactBytes, pos := 23036, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_115_t_tail0_decoded :
    instructionSequenceAt 1536 true { bytes := artifactBytes, pos := 22867, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[115]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 23036, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_115_e_tail10_decoded :
    instructionSequenceAt 1526 false { bytes := artifactBytes, pos := 23076, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[115]!).childBody true).drop 10, .end), { bytes := artifactBytes, pos := 23205, limit := 23603 }) := by
  cbv

end Project.EulerCertificate.Artifact
