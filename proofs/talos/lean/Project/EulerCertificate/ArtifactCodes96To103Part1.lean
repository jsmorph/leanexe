import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes96To103Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code98_seq_98_115_e_tail0_decoded :
    instructionSequenceAt 1536 false { bytes := artifactBytes, pos := 23036, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[115]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 23205, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_123_t_tail10_decoded :
    instructionSequenceAt 1518 true { bytes := artifactBytes, pos := 23264, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[123]!).childBody false).drop 10, .otherwise), { bytes := artifactBytes, pos := 23393, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_123_t_tail0_decoded :
    instructionSequenceAt 1528 true { bytes := artifactBytes, pos := 23224, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[123]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 23393, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_123_e_tail10_decoded :
    instructionSequenceAt 1518 false { bytes := artifactBytes, pos := 23433, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[123]!).childBody true).drop 10, .end), { bytes := artifactBytes, pos := 23562, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_123_e_tail0_decoded :
    instructionSequenceAt 1528 false { bytes := artifactBytes, pos := 23393, limit := 23603 } =
      .ok ((((((Cache.raw.codes[98]!).body)[123]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 23562, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_tail123_decoded :
    instructionSequenceAt 1530 false { bytes := artifactBytes, pos := 23222, limit := 23603 } =
      .ok ((((Cache.raw.codes[98]!).body).drop 123, .end), { bytes := artifactBytes, pos := 23603, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_tail115_decoded :
    instructionSequenceAt 1538 false { bytes := artifactBytes, pos := 22865, limit := 23603 } =
      .ok ((((Cache.raw.codes[98]!).body).drop 115, .end), { bytes := artifactBytes, pos := 23603, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_tail79_decoded :
    instructionSequenceAt 1574 false { bytes := artifactBytes, pos := 22452, limit := 23603 } =
      .ok ((((Cache.raw.codes[98]!).body).drop 79, .end), { bytes := artifactBytes, pos := 23603, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_tail71_decoded :
    instructionSequenceAt 1582 false { bytes := artifactBytes, pos := 22095, limit := 23603 } =
      .ok ((((Cache.raw.codes[98]!).body).drop 71, .end), { bytes := artifactBytes, pos := 23603, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_tail8_decoded :
    instructionSequenceAt 1645 false { bytes := artifactBytes, pos := 21966, limit := 23603 } =
      .ok ((((Cache.raw.codes[98]!).body).drop 8, .end), { bytes := artifactBytes, pos := 23603, limit := 23603 }) := by
  cbv

@[cbv_eval] theorem code98_seq_98_tail0_decoded :
    instructionSequenceAt 1653 false { bytes := artifactBytes, pos := 21950, limit := 23603 } =
      .ok ((((Cache.raw.codes[98]!).body).drop 0, .end), { bytes := artifactBytes, pos := 23603, limit := 23603 }) := by
  cbv

theorem code98_decoded :
    code { bytes := artifactBytes, pos := 21945, limit := 45644 } =
      .ok (Cache.raw.codes[98]!, { bytes := artifactBytes, pos := 23603, limit := 45644 }) := by
  refine code_eq_of_parts (size := 1656)
    (payload := { bytes := artifactBytes, pos := 21947, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 21950, limit := 23603 })
    (bodyFinish := { bytes := artifactBytes, pos := 23603, limit := 23603 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code98_seq_98_tail0_decoded
  · rfl

#print axioms code98_decoded

@[cbv_eval] theorem code99_seq_99_tail0_decoded :
    instructionSequenceAt 35 false { bytes := artifactBytes, pos := 23607, limit := 23642 } =
      .ok ((((Cache.raw.codes[99]!).body).drop 0, .end), { bytes := artifactBytes, pos := 23642, limit := 23642 }) := by
  cbv

theorem code99_decoded :
    code { bytes := artifactBytes, pos := 23603, limit := 45644 } =
      .ok (Cache.raw.codes[99]!, { bytes := artifactBytes, pos := 23642, limit := 45644 }) := by
  refine code_eq_of_parts (size := 38)
    (payload := { bytes := artifactBytes, pos := 23604, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 23607, limit := 23642 })
    (bodyFinish := { bytes := artifactBytes, pos := 23642, limit := 23642 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code99_seq_99_tail0_decoded
  · rfl

#print axioms code99_decoded

@[cbv_eval] theorem code100_seq_100_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 23646, limit := 23695 } =
      .ok ((((Cache.raw.codes[100]!).body).drop 0, .end), { bytes := artifactBytes, pos := 23695, limit := 23695 }) := by
  cbv

theorem code100_decoded :
    code { bytes := artifactBytes, pos := 23642, limit := 45644 } =
      .ok (Cache.raw.codes[100]!, { bytes := artifactBytes, pos := 23695, limit := 45644 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 23643, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 23646, limit := 23695 })
    (bodyFinish := { bytes := artifactBytes, pos := 23695, limit := 23695 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code100_seq_100_tail0_decoded
  · rfl

#print axioms code100_decoded

end Project.EulerCertificate.Artifact
