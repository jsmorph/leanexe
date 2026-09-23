import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_12_t_0_t_tail181 :
    instructionSequenceAt 1929 false { bytes := artifactBytes, pos := 3540, limit := 4612 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 181, .end), { bytes := artifactBytes, pos := 3668, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_12_t_0_t_tail133 :
    instructionSequenceAt 1977 false { bytes := artifactBytes, pos := 3392, limit := 4612 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 133, .end), { bytes := artifactBytes, pos := 3668, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_12_t_0_t_tail85 :
    instructionSequenceAt 2025 false { bytes := artifactBytes, pos := 3264, limit := 4612 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 85, .end), { bytes := artifactBytes, pos := 3668, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_12_t_0_t_tail48 :
    instructionSequenceAt 2062 false { bytes := artifactBytes, pos := 3135, limit := 4612 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 48, .end), { bytes := artifactBytes, pos := 3668, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_12_t_0_t_tail0 :
    instructionSequenceAt 2110 false { bytes := artifactBytes, pos := 3008, limit := 4612 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3668, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_12_t_0_t_tail181 :
    instructionSequenceAt 1929 false { bytes := artifactBytes, pos := 4372, limit := 4612 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 181, .end), { bytes := artifactBytes, pos := 4500, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_12_t_0_t_tail133 :
    instructionSequenceAt 1977 false { bytes := artifactBytes, pos := 4224, limit := 4612 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 133, .end), { bytes := artifactBytes, pos := 4500, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_12_t_0_t_tail85 :
    instructionSequenceAt 2025 false { bytes := artifactBytes, pos := 4096, limit := 4612 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 85, .end), { bytes := artifactBytes, pos := 4500, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_12_t_0_t_tail48 :
    instructionSequenceAt 2062 false { bytes := artifactBytes, pos := 3967, limit := 4612 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 48, .end), { bytes := artifactBytes, pos := 4500, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_12_t_0_t_tail0 :
    instructionSequenceAt 2110 false { bytes := artifactBytes, pos := 3840, limit := 4612 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4500, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_12_t_tail0 :
    instructionSequenceAt 2112 false { bytes := artifactBytes, pos := 3006, limit := 4612 } =
      .ok ((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3669, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_12_t_tail0 :
    instructionSequenceAt 2112 false { bytes := artifactBytes, pos := 3838, limit := 4612 } =
      .ok ((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4501, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_tail21 :
    instructionSequenceAt 2105 true { bytes := artifactBytes, pos := 3683, limit := 4612 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 21, .otherwise), { bytes := artifactBytes, pos := 3812, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_tail12 :
    instructionSequenceAt 2114 true { bytes := artifactBytes, pos := 3004, limit := 4612 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 12, .otherwise), { bytes := artifactBytes, pos := 3812, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_tail0 :
    instructionSequenceAt 2126 true { bytes := artifactBytes, pos := 2980, limit := 4612 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3812, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_tail12 :
    instructionSequenceAt 2114 false { bytes := artifactBytes, pos := 3836, limit := 4612 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 12, .end), { bytes := artifactBytes, pos := 4512, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_tail0 :
    instructionSequenceAt 2126 false { bytes := artifactBytes, pos := 3812, limit := 4612 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 4512, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_86_t_0_t_tail18 :
    instructionSequenceAt 2142 false { bytes := artifactBytes, pos := 2643, limit := 4612 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[86]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 2771, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_86_t_0_t_tail0 :
    instructionSequenceAt 2160 false { bytes := artifactBytes, pos := 2612, limit := 4612 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[86]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2771, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_tail19 :
    instructionSequenceAt 2128 false { bytes := artifactBytes, pos := 2978, limit := 4612 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := artifactBytes, pos := 4526, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_tail0 :
    instructionSequenceAt 2147 false { bytes := artifactBytes, pos := 2942, limit := 4612 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4526, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_86_t_tail0 :
    instructionSequenceAt 2162 false { bytes := artifactBytes, pos := 2610, limit := 4612 } =
      .ok ((((((Cache.raw.codes[8]!).body)[86]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2772, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_90_t_tail8 :
    instructionSequenceAt 2150 true { bytes := artifactBytes, pos := 2792, limit := 4612 } =
      .ok ((((((Cache.raw.codes[8]!).body)[90]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 2923, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_90_t_tail0 :
    instructionSequenceAt 2158 true { bytes := artifactBytes, pos := 2779, limit := 4612 } =
      .ok ((((((Cache.raw.codes[8]!).body)[90]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2923, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_tail0 :
    instructionSequenceAt 2149 false { bytes := artifactBytes, pos := 2940, limit := 4612 } =
      .ok ((((((Cache.raw.codes[8]!).body)[99]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4527, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail99 :
    instructionSequenceAt 2151 false { bytes := artifactBytes, pos := 2938, limit := 4612 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 99, .end), { bytes := artifactBytes, pos := 4612, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail90 :
    instructionSequenceAt 2160 false { bytes := artifactBytes, pos := 2777, limit := 4612 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 90, .end), { bytes := artifactBytes, pos := 4612, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail86 :
    instructionSequenceAt 2164 false { bytes := artifactBytes, pos := 2608, limit := 4612 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 86, .end), { bytes := artifactBytes, pos := 4612, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail43 :
    instructionSequenceAt 2207 false { bytes := artifactBytes, pos := 2479, limit := 4612 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 43, .end), { bytes := artifactBytes, pos := 4612, limit := 4612 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail0 :
    instructionSequenceAt 2250 false { bytes := artifactBytes, pos := 2362, limit := 4612 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4612, limit := 4612 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 2357, limit := 5441 } = .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 4612, limit := 5441 }) := by
  refine code_eq_of_parts (size := 2253)
    (payload := { bytes := artifactBytes, pos := 2359, limit := 5441 })
    (bodyStart := { bytes := artifactBytes, pos := 2362, limit := 4612 })
    (bodyFinish := { bytes := artifactBytes, pos := 4612, limit := 4612 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_8_tail0
  · rfl

#print axioms code8_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
