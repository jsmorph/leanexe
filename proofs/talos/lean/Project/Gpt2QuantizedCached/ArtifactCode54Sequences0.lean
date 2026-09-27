import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_125_e_138_t_0_t_tail23 :
    instructionSequenceAt 2164 false { bytes := artifactBytes, pos := 22770, limit := 23617 } =
      .ok ((((((((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true)[125]!).childBody true)[138]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := artifactBytes, pos := 22905, limit := 23617 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_125_e_138_t_0_t_tail0 :
    instructionSequenceAt 2187 false { bytes := artifactBytes, pos := 22721, limit := 23617 } =
      .ok ((((((((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true)[125]!).childBody true)[138]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 22905, limit := 23617 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_125_e_138_t_tail0 :
    instructionSequenceAt 2189 false { bytes := artifactBytes, pos := 22719, limit := 23617 } =
      .ok ((((((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true)[125]!).childBody true)[138]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 22906, limit := 23617 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_125_e_142_t_tail14 :
    instructionSequenceAt 2171 true { bytes := artifactBytes, pos := 22944, limit := 23617 } =
      .ok ((((((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true)[125]!).childBody true)[142]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 23073, limit := 23617 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_125_e_142_t_tail0 :
    instructionSequenceAt 2185 true { bytes := artifactBytes, pos := 22914, limit := 23617 } =
      .ok ((((((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true)[125]!).childBody true)[142]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23073, limit := 23617 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_125_e_tail151 :
    instructionSequenceAt 2178 false { bytes := artifactBytes, pos := 23091, limit := 23617 } =
      .ok ((((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true)[125]!).childBody true).drop 151, .end), { bytes := artifactBytes, pos := 23264, limit := 23617 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_125_e_tail142 :
    instructionSequenceAt 2187 false { bytes := artifactBytes, pos := 22912, limit := 23617 } =
      .ok ((((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true)[125]!).childBody true).drop 142, .end), { bytes := artifactBytes, pos := 23264, limit := 23617 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_125_e_tail138 :
    instructionSequenceAt 2191 false { bytes := artifactBytes, pos := 22717, limit := 23617 } =
      .ok ((((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true)[125]!).childBody true).drop 138, .end), { bytes := artifactBytes, pos := 23264, limit := 23617 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
