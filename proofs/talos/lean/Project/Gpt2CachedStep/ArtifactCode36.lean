import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_36_75_t_0_t_110_t_0_t_tail18 :
    instructionSequenceAt 2132 false { bytes := artifactBytes, pos := 15580, limit := 16952 } =
      .ok ((((((((((((Cache.raw.codes[36]!).body)[75]!).childBody false)[0]!).childBody false)[110]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 15708, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_75_t_0_t_110_t_0_t_tail0 :
    instructionSequenceAt 2150 false { bytes := artifactBytes, pos := 15549, limit := 16952 } =
      .ok ((((((((((((Cache.raw.codes[36]!).body)[75]!).childBody false)[0]!).childBody false)[110]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15708, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_75_t_0_t_110_t_tail0 :
    instructionSequenceAt 2152 false { bytes := artifactBytes, pos := 15547, limit := 16952 } =
      .ok ((((((((((Cache.raw.codes[36]!).body)[75]!).childBody false)[0]!).childBody false)[110]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15709, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_75_t_0_t_114_t_tail8 :
    instructionSequenceAt 2140 true { bytes := artifactBytes, pos := 15729, limit := 16952 } =
      .ok ((((((((((Cache.raw.codes[36]!).body)[75]!).childBody false)[0]!).childBody false)[114]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 15860, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_75_t_0_t_114_t_tail0 :
    instructionSequenceAt 2148 true { bytes := artifactBytes, pos := 15716, limit := 16952 } =
      .ok ((((((((((Cache.raw.codes[36]!).body)[75]!).childBody false)[0]!).childBody false)[114]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15860, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_29_t_0_t_tail18 :
    instructionSequenceAt 2292 false { bytes := artifactBytes, pos := 14725, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[29]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 14853, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_29_t_0_t_tail0 :
    instructionSequenceAt 2310 false { bytes := artifactBytes, pos := 14694, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[29]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14853, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_42_t_0_t_tail43 :
    instructionSequenceAt 2254 false { bytes := artifactBytes, pos := 15129, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[42]!).childBody false)[0]!).childBody false).drop 43, .end), { bytes := artifactBytes, pos := 15257, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_42_t_0_t_tail0 :
    instructionSequenceAt 2297 false { bytes := artifactBytes, pos := 15024, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[42]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15257, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_75_t_0_t_tail174 :
    instructionSequenceAt 2090 false { bytes := artifactBytes, pos := 16169, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[75]!).childBody false)[0]!).childBody false).drop 174, .end), { bytes := artifactBytes, pos := 16298, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_75_t_0_t_tail155 :
    instructionSequenceAt 2109 false { bytes := artifactBytes, pos := 16035, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[75]!).childBody false)[0]!).childBody false).drop 155, .end), { bytes := artifactBytes, pos := 16298, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_75_t_0_t_tail123 :
    instructionSequenceAt 2141 false { bytes := artifactBytes, pos := 15875, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[75]!).childBody false)[0]!).childBody false).drop 123, .end), { bytes := artifactBytes, pos := 16298, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_75_t_0_t_tail114 :
    instructionSequenceAt 2150 false { bytes := artifactBytes, pos := 15714, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[75]!).childBody false)[0]!).childBody false).drop 114, .end), { bytes := artifactBytes, pos := 16298, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_75_t_0_t_tail110 :
    instructionSequenceAt 2154 false { bytes := artifactBytes, pos := 15545, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[75]!).childBody false)[0]!).childBody false).drop 110, .end), { bytes := artifactBytes, pos := 16298, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_75_t_0_t_tail46 :
    instructionSequenceAt 2218 false { bytes := artifactBytes, pos := 15417, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[75]!).childBody false)[0]!).childBody false).drop 46, .end), { bytes := artifactBytes, pos := 16298, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_75_t_0_t_tail0 :
    instructionSequenceAt 2264 false { bytes := artifactBytes, pos := 15326, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[75]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16298, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_142_t_0_t_tail18 :
    instructionSequenceAt 2179 false { bytes := artifactBytes, pos := 16466, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[142]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 16594, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_142_t_0_t_tail0 :
    instructionSequenceAt 2197 false { bytes := artifactBytes, pos := 16435, limit := 16952 } =
      .ok ((((((((Cache.raw.codes[36]!).body)[142]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16594, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_29_t_tail0 :
    instructionSequenceAt 2312 false { bytes := artifactBytes, pos := 14692, limit := 16952 } =
      .ok ((((((Cache.raw.codes[36]!).body)[29]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14854, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_33_t_tail8 :
    instructionSequenceAt 2300 true { bytes := artifactBytes, pos := 14874, limit := 16952 } =
      .ok ((((((Cache.raw.codes[36]!).body)[33]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 15005, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_33_t_tail0 :
    instructionSequenceAt 2308 true { bytes := artifactBytes, pos := 14861, limit := 16952 } =
      .ok ((((((Cache.raw.codes[36]!).body)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15005, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_42_t_tail0 :
    instructionSequenceAt 2299 false { bytes := artifactBytes, pos := 15022, limit := 16952 } =
      .ok ((((((Cache.raw.codes[36]!).body)[42]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15258, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_75_t_tail0 :
    instructionSequenceAt 2266 false { bytes := artifactBytes, pos := 15324, limit := 16952 } =
      .ok ((((((Cache.raw.codes[36]!).body)[75]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16299, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_142_t_tail0 :
    instructionSequenceAt 2199 false { bytes := artifactBytes, pos := 16433, limit := 16952 } =
      .ok ((((((Cache.raw.codes[36]!).body)[142]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16595, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_146_t_tail8 :
    instructionSequenceAt 2187 true { bytes := artifactBytes, pos := 16615, limit := 16952 } =
      .ok ((((((Cache.raw.codes[36]!).body)[146]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 16746, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_146_t_tail0 :
    instructionSequenceAt 2195 true { bytes := artifactBytes, pos := 16602, limit := 16952 } =
      .ok ((((((Cache.raw.codes[36]!).body)[146]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16746, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_tail158 :
    instructionSequenceAt 2185 false { bytes := artifactBytes, pos := 16805, limit := 16952 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 158, .end), { bytes := artifactBytes, pos := 16952, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_tail146 :
    instructionSequenceAt 2197 false { bytes := artifactBytes, pos := 16600, limit := 16952 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 146, .end), { bytes := artifactBytes, pos := 16952, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_tail142 :
    instructionSequenceAt 2201 false { bytes := artifactBytes, pos := 16431, limit := 16952 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 142, .end), { bytes := artifactBytes, pos := 16952, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_tail78 :
    instructionSequenceAt 2265 false { bytes := artifactBytes, pos := 16303, limit := 16952 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 78, .end), { bytes := artifactBytes, pos := 16952, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_tail75 :
    instructionSequenceAt 2268 false { bytes := artifactBytes, pos := 15322, limit := 16952 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 75, .end), { bytes := artifactBytes, pos := 16952, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_tail42 :
    instructionSequenceAt 2301 false { bytes := artifactBytes, pos := 15020, limit := 16952 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 42, .end), { bytes := artifactBytes, pos := 16952, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_tail33 :
    instructionSequenceAt 2310 false { bytes := artifactBytes, pos := 14859, limit := 16952 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 33, .end), { bytes := artifactBytes, pos := 16952, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_tail29 :
    instructionSequenceAt 2314 false { bytes := artifactBytes, pos := 14690, limit := 16952 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 29, .end), { bytes := artifactBytes, pos := 16952, limit := 16952 }) := by
  cbv

@[cbv_eval] theorem sequence_36_tail0 :
    instructionSequenceAt 2343 false { bytes := artifactBytes, pos := 14609, limit := 16952 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16952, limit := 16952 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 14604, limit := 19083 } = .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 16952, limit := 19083 }) := by
  refine code_eq_of_parts (size := 2346)
    (payload := { bytes := artifactBytes, pos := 14606, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 14609, limit := 16952 })
    (bodyFinish := { bytes := artifactBytes, pos := 16952, limit := 16952 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_36_tail0
  · rfl

#print axioms code36_decoded

end Project.Gpt2CachedStep.Artifact
