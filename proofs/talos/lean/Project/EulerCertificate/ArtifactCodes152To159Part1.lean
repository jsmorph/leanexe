import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes152To159Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code158_decoded :
    code { bytes := artifactBytes, pos := 30920, limit := 45644 } =
      .ok (Cache.raw.codes[158]!, { bytes := artifactBytes, pos := 31387, limit := 45644 }) := by
  refine code_eq_of_parts (size := 465)
    (payload := { bytes := artifactBytes, pos := 30922, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 30925, limit := 31387 })
    (bodyFinish := { bytes := artifactBytes, pos := 31387, limit := 31387 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code158_seq_158_tail0_decoded
  · rfl

#print axioms code158_decoded

@[cbv_eval] theorem code159_seq_159_30_t_0_t_tail18_decoded :
    instructionSequenceAt 786 false { bytes := artifactBytes, pos := 31485, limit := 32230 } =
      .ok ((((((((Cache.raw.codes[159]!).body)[30]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 31613, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_30_t_0_t_tail0_decoded :
    instructionSequenceAt 804 false { bytes := artifactBytes, pos := 31454, limit := 32230 } =
      .ok ((((((((Cache.raw.codes[159]!).body)[30]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 31613, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_47_t_0_t_tail162_decoded :
    instructionSequenceAt 625 false { bytes := artifactBytes, pos := 32084, limit := 32230 } =
      .ok ((((((((Cache.raw.codes[159]!).body)[47]!).childBody false)[0]!).childBody false).drop 162, .end), { bytes := artifactBytes, pos := 32212, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_47_t_0_t_tail96_decoded :
    instructionSequenceAt 691 false { bytes := artifactBytes, pos := 31955, limit := 32230 } =
      .ok ((((((((Cache.raw.codes[159]!).body)[47]!).childBody false)[0]!).childBody false).drop 96, .end), { bytes := artifactBytes, pos := 32212, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_47_t_0_t_tail20_decoded :
    instructionSequenceAt 767 false { bytes := artifactBytes, pos := 31826, limit := 32230 } =
      .ok ((((((((Cache.raw.codes[159]!).body)[47]!).childBody false)[0]!).childBody false).drop 20, .end), { bytes := artifactBytes, pos := 32212, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_47_t_0_t_tail0_decoded :
    instructionSequenceAt 787 false { bytes := artifactBytes, pos := 31792, limit := 32230 } =
      .ok ((((((((Cache.raw.codes[159]!).body)[47]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 32212, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_30_t_tail0_decoded :
    instructionSequenceAt 806 false { bytes := artifactBytes, pos := 31452, limit := 32230 } =
      .ok ((((((Cache.raw.codes[159]!).body)[30]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 31614, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_34_t_tail8_decoded :
    instructionSequenceAt 794 true { bytes := artifactBytes, pos := 31634, limit := 32230 } =
      .ok ((((((Cache.raw.codes[159]!).body)[34]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 31765, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_34_t_tail0_decoded :
    instructionSequenceAt 802 true { bytes := artifactBytes, pos := 31621, limit := 32230 } =
      .ok ((((((Cache.raw.codes[159]!).body)[34]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 31765, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_47_t_tail0_decoded :
    instructionSequenceAt 789 false { bytes := artifactBytes, pos := 31790, limit := 32230 } =
      .ok ((((((Cache.raw.codes[159]!).body)[47]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 32213, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_tail47_decoded :
    instructionSequenceAt 791 false { bytes := artifactBytes, pos := 31788, limit := 32230 } =
      .ok ((((Cache.raw.codes[159]!).body).drop 47, .end), { bytes := artifactBytes, pos := 32230, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_tail34_decoded :
    instructionSequenceAt 804 false { bytes := artifactBytes, pos := 31619, limit := 32230 } =
      .ok ((((Cache.raw.codes[159]!).body).drop 34, .end), { bytes := artifactBytes, pos := 32230, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_tail30_decoded :
    instructionSequenceAt 808 false { bytes := artifactBytes, pos := 31450, limit := 32230 } =
      .ok ((((Cache.raw.codes[159]!).body).drop 30, .end), { bytes := artifactBytes, pos := 32230, limit := 32230 }) := by
  cbv

@[cbv_eval] theorem code159_seq_159_tail0_decoded :
    instructionSequenceAt 838 false { bytes := artifactBytes, pos := 31392, limit := 32230 } =
      .ok ((((Cache.raw.codes[159]!).body).drop 0, .end), { bytes := artifactBytes, pos := 32230, limit := 32230 }) := by
  cbv

theorem code159_decoded :
    code { bytes := artifactBytes, pos := 31387, limit := 45644 } =
      .ok (Cache.raw.codes[159]!, { bytes := artifactBytes, pos := 32230, limit := 45644 }) := by
  refine code_eq_of_parts (size := 841)
    (payload := { bytes := artifactBytes, pos := 31389, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 31392, limit := 32230 })
    (bodyFinish := { bytes := artifactBytes, pos := 32230, limit := 32230 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code159_seq_159_tail0_decoded
  · rfl

#print axioms code159_decoded

end Project.EulerCertificate.Artifact
