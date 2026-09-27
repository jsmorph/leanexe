import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_26_35_t_0_t_30_t_0_t_tail161 :
    instructionSequenceAt 1671 false { bytes := artifactBytes, pos := 11753, limit := 12826 } =
      .ok ((((((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false)[30]!).childBody false)[0]!).childBody false).drop 161, .end), { bytes := artifactBytes, pos := 11882, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_30_t_0_t_tail121 :
    instructionSequenceAt 1711 false { bytes := artifactBytes, pos := 11625, limit := 12826 } =
      .ok ((((((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false)[30]!).childBody false)[0]!).childBody false).drop 121, .end), { bytes := artifactBytes, pos := 11882, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_30_t_0_t_tail103 :
    instructionSequenceAt 1729 false { bytes := artifactBytes, pos := 11493, limit := 12826 } =
      .ok ((((((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false)[30]!).childBody false)[0]!).childBody false).drop 103, .end), { bytes := artifactBytes, pos := 11882, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_30_t_0_t_tail84 :
    instructionSequenceAt 1748 false { bytes := artifactBytes, pos := 11365, limit := 12826 } =
      .ok ((((((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false)[30]!).childBody false)[0]!).childBody false).drop 84, .end), { bytes := artifactBytes, pos := 11882, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_30_t_0_t_tail56 :
    instructionSequenceAt 1776 false { bytes := artifactBytes, pos := 11207, limit := 12826 } =
      .ok ((((((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false)[30]!).childBody false)[0]!).childBody false).drop 56, .end), { bytes := artifactBytes, pos := 11882, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_30_t_0_t_tail0 :
    instructionSequenceAt 1832 false { bytes := artifactBytes, pos := 11084, limit := 12826 } =
      .ok ((((((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false)[30]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11882, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_30_t_tail0 :
    instructionSequenceAt 1834 false { bytes := artifactBytes, pos := 11082, limit := 12826 } =
      .ok ((((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false)[30]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11883, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_35_t_0_t_tail159 :
    instructionSequenceAt 1707 false { bytes := artifactBytes, pos := 12572, limit := 12826 } =
      .ok ((((((((Cache.raw.codes[26]!).body)[35]!).childBody false)[0]!).childBody false).drop 159, .end), { bytes := artifactBytes, pos := 12707, limit := 12826 }) := by
  cbv


end Project.Beck.Artifact
