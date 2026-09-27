import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode26Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_26_35_t_0_t_tail143 :
    instructionSequenceAt 1723 false { bytes := artifactBytes, pos := 12444, limit := 12826 } =
      .ok ((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false).drop 143, .end), { bytes := artifactBytes, pos := 12707, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_tail125 :
    instructionSequenceAt 1741 false { bytes := artifactBytes, pos := 12310, limit := 12826 } =
      .ok ((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false).drop 125, .end), { bytes := artifactBytes, pos := 12707, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_tail102 :
    instructionSequenceAt 1764 false { bytes := artifactBytes, pos := 12177, limit := 12826 } =
      .ok ((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false).drop 102, .end), { bytes := artifactBytes, pos := 12707, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_tail84 :
    instructionSequenceAt 1782 false { bytes := artifactBytes, pos := 12049, limit := 12826 } =
      .ok ((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false).drop 84, .end), { bytes := artifactBytes, pos := 12707, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_tail50 :
    instructionSequenceAt 1816 false { bytes := artifactBytes, pos := 11921, limit := 12826 } =
      .ok ((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false).drop 50, .end), { bytes := artifactBytes, pos := 12707, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_tail30 :
    instructionSequenceAt 1836 false { bytes := artifactBytes, pos := 11080, limit := 12826 } =
      .ok ((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false).drop 30, .end), { bytes := artifactBytes, pos := 12707, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_tail0 :
    instructionSequenceAt 1866 false { bytes := artifactBytes, pos := 11013, limit := 12826 } =
      .ok ((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12707, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_tail0 :
    instructionSequenceAt 1868 false { bytes := artifactBytes, pos := 11011, limit := 12826 } =
      .ok ((((((Cache.raw.codes[26]!).body)[35]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12708, limit := 12826 }) := by
  cbv


end Project.Beck.Artifact
