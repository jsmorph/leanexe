import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_20_91_t_0_t_26_t_0_t_tail33 :
    instructionSequenceAt 1977 false { bytes := artifactBytes, pos := 3006, limit := 4096 } =
      .ok ((((((((((((Cache.raw.codes[20]!).body)[91]!).childBody false)[0]!).childBody false)[26]!).childBody false)[0]!).childBody false).drop 33, .end), { bytes := artifactBytes, pos := 3134, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_91_t_0_t_26_t_0_t_tail0 :
    instructionSequenceAt 2010 false { bytes := artifactBytes, pos := 2916, limit := 4096 } =
      .ok ((((((((((((Cache.raw.codes[20]!).body)[91]!).childBody false)[0]!).childBody false)[26]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3134, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_91_t_0_t_26_t_tail0 :
    instructionSequenceAt 2012 false { bytes := artifactBytes, pos := 2914, limit := 4096 } =
      .ok ((((((((((Cache.raw.codes[20]!).body)[91]!).childBody false)[0]!).childBody false)[26]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3135, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_29_t_0_t_tail18 :
    instructionSequenceAt 2084 false { bytes := artifactBytes, pos := 2076, limit := 4096 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[29]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 2204, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_29_t_0_t_tail0 :
    instructionSequenceAt 2102 false { bytes := artifactBytes, pos := 2045, limit := 4096 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[29]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2204, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_78_t_0_t_tail18 :
    instructionSequenceAt 2035 false { bytes := artifactBytes, pos := 2562, limit := 4096 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[78]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 2690, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_78_t_0_t_tail0 :
    instructionSequenceAt 2053 false { bytes := artifactBytes, pos := 2531, limit := 4096 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[78]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2690, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_91_t_0_t_tail26 :
    instructionSequenceAt 2014 false { bytes := artifactBytes, pos := 2912, limit := 4096 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[91]!).childBody false)[0]!).childBody false).drop 26, .end), { bytes := artifactBytes, pos := 3228, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_91_t_0_t_tail0 :
    instructionSequenceAt 2040 false { bytes := artifactBytes, pos := 2861, limit := 4096 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[91]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3228, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_134_t_0_t_tail18 :
    instructionSequenceAt 1979 false { bytes := artifactBytes, pos := 3392, limit := 4096 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[134]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 3520, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_134_t_0_t_tail0 :
    instructionSequenceAt 1997 false { bytes := artifactBytes, pos := 3361, limit := 4096 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[134]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3520, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_147_t_0_t_tail97 :
    instructionSequenceAt 1887 false { bytes := artifactBytes, pos := 3891, limit := 4096 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[147]!).childBody false)[0]!).childBody false).drop 97, .end), { bytes := artifactBytes, pos := 4020, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_147_t_0_t_tail39 :
    instructionSequenceAt 1945 false { bytes := artifactBytes, pos := 3763, limit := 4096 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[147]!).childBody false)[0]!).childBody false).drop 39, .end), { bytes := artifactBytes, pos := 4020, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_147_t_0_t_tail0 :
    instructionSequenceAt 1984 false { bytes := artifactBytes, pos := 3691, limit := 4096 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[147]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4020, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_29_t_tail0 :
    instructionSequenceAt 2104 false { bytes := artifactBytes, pos := 2043, limit := 4096 } =
      .ok ((((((Cache.raw.codes[20]!).body)[29]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2205, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_33_t_tail8 :
    instructionSequenceAt 2092 true { bytes := artifactBytes, pos := 2225, limit := 4096 } =
      .ok ((((((Cache.raw.codes[20]!).body)[33]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 2356, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_33_t_tail0 :
    instructionSequenceAt 2100 true { bytes := artifactBytes, pos := 2212, limit := 4096 } =
      .ok ((((((Cache.raw.codes[20]!).body)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2356, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_78_t_tail0 :
    instructionSequenceAt 2055 false { bytes := artifactBytes, pos := 2529, limit := 4096 } =
      .ok ((((((Cache.raw.codes[20]!).body)[78]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2691, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_82_t_tail8 :
    instructionSequenceAt 2043 true { bytes := artifactBytes, pos := 2711, limit := 4096 } =
      .ok ((((((Cache.raw.codes[20]!).body)[82]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 2842, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_82_t_tail0 :
    instructionSequenceAt 2051 true { bytes := artifactBytes, pos := 2698, limit := 4096 } =
      .ok ((((((Cache.raw.codes[20]!).body)[82]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2842, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_91_t_tail0 :
    instructionSequenceAt 2042 false { bytes := artifactBytes, pos := 2859, limit := 4096 } =
      .ok ((((((Cache.raw.codes[20]!).body)[91]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3229, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_134_t_tail0 :
    instructionSequenceAt 1999 false { bytes := artifactBytes, pos := 3359, limit := 4096 } =
      .ok ((((((Cache.raw.codes[20]!).body)[134]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3521, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_138_t_tail8 :
    instructionSequenceAt 1987 true { bytes := artifactBytes, pos := 3541, limit := 4096 } =
      .ok ((((((Cache.raw.codes[20]!).body)[138]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 3672, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_138_t_tail0 :
    instructionSequenceAt 1995 true { bytes := artifactBytes, pos := 3528, limit := 4096 } =
      .ok ((((((Cache.raw.codes[20]!).body)[138]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3672, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_147_t_tail0 :
    instructionSequenceAt 1986 false { bytes := artifactBytes, pos := 3689, limit := 4096 } =
      .ok ((((((Cache.raw.codes[20]!).body)[147]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4021, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail147 :
    instructionSequenceAt 1988 false { bytes := artifactBytes, pos := 3687, limit := 4096 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 147, .end), { bytes := artifactBytes, pos := 4096, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail138 :
    instructionSequenceAt 1997 false { bytes := artifactBytes, pos := 3526, limit := 4096 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 138, .end), { bytes := artifactBytes, pos := 4096, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail134 :
    instructionSequenceAt 2001 false { bytes := artifactBytes, pos := 3357, limit := 4096 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 134, .end), { bytes := artifactBytes, pos := 4096, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail92 :
    instructionSequenceAt 2043 false { bytes := artifactBytes, pos := 3229, limit := 4096 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 92, .end), { bytes := artifactBytes, pos := 4096, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail91 :
    instructionSequenceAt 2044 false { bytes := artifactBytes, pos := 2857, limit := 4096 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 91, .end), { bytes := artifactBytes, pos := 4096, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail82 :
    instructionSequenceAt 2053 false { bytes := artifactBytes, pos := 2696, limit := 4096 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 82, .end), { bytes := artifactBytes, pos := 4096, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail78 :
    instructionSequenceAt 2057 false { bytes := artifactBytes, pos := 2527, limit := 4096 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 78, .end), { bytes := artifactBytes, pos := 4096, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail42 :
    instructionSequenceAt 2093 false { bytes := artifactBytes, pos := 2371, limit := 4096 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 42, .end), { bytes := artifactBytes, pos := 4096, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail33 :
    instructionSequenceAt 2102 false { bytes := artifactBytes, pos := 2210, limit := 4096 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 33, .end), { bytes := artifactBytes, pos := 4096, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail29 :
    instructionSequenceAt 2106 false { bytes := artifactBytes, pos := 2041, limit := 4096 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 29, .end), { bytes := artifactBytes, pos := 4096, limit := 4096 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail0 :
    instructionSequenceAt 2135 false { bytes := artifactBytes, pos := 1961, limit := 4096 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4096, limit := 4096 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 1956, limit := 19083 } = .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 4096, limit := 19083 }) := by
  refine code_eq_of_parts (size := 2138)
    (payload := { bytes := artifactBytes, pos := 1958, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 1961, limit := 4096 })
    (bodyFinish := { bytes := artifactBytes, pos := 4096, limit := 4096 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_20_tail0
  · rfl

#print axioms code20_decoded

end Project.Gpt2CachedStep.Artifact
