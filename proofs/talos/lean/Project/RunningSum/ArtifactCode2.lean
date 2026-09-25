import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_73_t_0_t_tail23 :
    instructionSequenceAt 4073 false { bytes := bytes, pos := 4115, limit := 6064 } =
      .ok ((((((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false)[73]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := bytes, pos := 4250, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_73_t_0_t_tail0 :
    instructionSequenceAt 4096 false { bytes := bytes, pos := 4066, limit := 6064 } =
      .ok ((((((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false)[73]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 4250, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_73_t_0_t_tail23 :
    instructionSequenceAt 4138 false { bytes := bytes, pos := 5393, limit := 6064 } =
      .ok ((((((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false)[73]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := bytes, pos := 5528, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_73_t_0_t_tail0 :
    instructionSequenceAt 4161 false { bytes := bytes, pos := 5344, limit := 6064 } =
      .ok ((((((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false)[73]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 5528, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_76_t_0_t_tail23 :
    instructionSequenceAt 4194 false { bytes := bytes, pos := 2256, limit := 6064 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false)[76]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := bytes, pos := 2391, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_76_t_0_t_tail0 :
    instructionSequenceAt 4217 false { bytes := bytes, pos := 2207, limit := 6064 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false)[76]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 2391, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_73_t_tail0 :
    instructionSequenceAt 4098 false { bytes := bytes, pos := 4064, limit := 6064 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false)[73]!).childBody false).drop 0, .end), { bytes := bytes, pos := 4251, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_77_t_tail14 :
    instructionSequenceAt 4080 true { bytes := bytes, pos := 4289, limit := 6064 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false)[77]!).childBody false).drop 14, .end), { bytes := bytes, pos := 4418, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_77_t_tail0 :
    instructionSequenceAt 4094 true { bytes := bytes, pos := 4259, limit := 6064 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false)[77]!).childBody false).drop 0, .end), { bytes := bytes, pos := 4418, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_73_t_tail0 :
    instructionSequenceAt 4163 false { bytes := bytes, pos := 5342, limit := 6064 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false)[73]!).childBody false).drop 0, .end), { bytes := bytes, pos := 5529, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_77_t_tail14 :
    instructionSequenceAt 4145 true { bytes := bytes, pos := 5567, limit := 6064 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false)[77]!).childBody false).drop 14, .end), { bytes := bytes, pos := 5696, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_77_t_tail0 :
    instructionSequenceAt 4159 true { bytes := bytes, pos := 5537, limit := 6064 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false)[77]!).childBody false).drop 0, .end), { bytes := bytes, pos := 5696, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_76_t_tail0 :
    instructionSequenceAt 4219 false { bytes := bytes, pos := 2205, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false)[76]!).childBody false).drop 0, .end), { bytes := bytes, pos := 2392, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_80_t_tail14 :
    instructionSequenceAt 4201 true { bytes := bytes, pos := 2430, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false)[80]!).childBody false).drop 14, .end), { bytes := bytes, pos := 2559, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_80_t_tail0 :
    instructionSequenceAt 4215 true { bytes := bytes, pos := 2400, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false)[80]!).childBody false).drop 0, .end), { bytes := bytes, pos := 2559, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_36_t_0_t_tail23 :
    instructionSequenceAt 4208 false { bytes := bytes, pos := 3105, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[36]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := bytes, pos := 3240, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_36_t_0_t_tail0 :
    instructionSequenceAt 4231 false { bytes := bytes, pos := 3056, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[36]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 3240, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_69_t_0_t_tail19 :
    instructionSequenceAt 4179 false { bytes := bytes, pos := 3674, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[69]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := bytes, pos := 3805, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_69_t_0_t_tail5 :
    instructionSequenceAt 4193 false { bytes := bytes, pos := 3522, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[69]!).childBody false)[0]!).childBody false).drop 5, .end), { bytes := bytes, pos := 3805, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_69_t_0_t_tail0 :
    instructionSequenceAt 4198 false { bytes := bytes, pos := 3513, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[69]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 3805, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_tail114 :
    instructionSequenceAt 4059 false { bytes := bytes, pos := 4537, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false).drop 114, .end), { bytes := bytes, pos := 4667, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_tail77 :
    instructionSequenceAt 4096 false { bytes := bytes, pos := 4257, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false).drop 77, .end), { bytes := bytes, pos := 4667, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_tail73 :
    instructionSequenceAt 4100 false { bytes := bytes, pos := 4062, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false).drop 73, .end), { bytes := bytes, pos := 4667, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_tail28 :
    instructionSequenceAt 4145 false { bytes := bytes, pos := 3933, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false).drop 28, .end), { bytes := bytes, pos := 4667, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_tail0 :
    instructionSequenceAt 4173 false { bytes := bytes, pos := 3859, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 4667, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_4_t_0_t_tail19 :
    instructionSequenceAt 4244 false { bytes := bytes, pos := 4952, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[4]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := bytes, pos := 5083, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_4_t_0_t_tail5 :
    instructionSequenceAt 4258 false { bytes := bytes, pos := 4800, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[4]!).childBody false)[0]!).childBody false).drop 5, .end), { bytes := bytes, pos := 5083, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_4_t_0_t_tail0 :
    instructionSequenceAt 4263 false { bytes := bytes, pos := 4791, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[4]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 5083, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_tail114 :
    instructionSequenceAt 4124 false { bytes := bytes, pos := 5815, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false).drop 114, .end), { bytes := bytes, pos := 5945, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_tail77 :
    instructionSequenceAt 4161 false { bytes := bytes, pos := 5535, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false).drop 77, .end), { bytes := bytes, pos := 5945, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_tail73 :
    instructionSequenceAt 4165 false { bytes := bytes, pos := 5340, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false).drop 73, .end), { bytes := bytes, pos := 5945, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_tail28 :
    instructionSequenceAt 4210 false { bytes := bytes, pos := 5211, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false).drop 28, .end), { bytes := bytes, pos := 5945, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_tail0 :
    instructionSequenceAt 4238 false { bytes := bytes, pos := 5137, limit := 6064 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 5945, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail129 :
    instructionSequenceAt 4168 false { bytes := bytes, pos := 2759, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 129, .end), { bytes := bytes, pos := 2887, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail92 :
    instructionSequenceAt 4205 false { bytes := bytes, pos := 2631, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 92, .end), { bytes := bytes, pos := 2887, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail80 :
    instructionSequenceAt 4217 false { bytes := bytes, pos := 2398, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 80, .end), { bytes := bytes, pos := 2887, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail76 :
    instructionSequenceAt 4221 false { bytes := bytes, pos := 2203, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 76, .end), { bytes := bytes, pos := 2887, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail31 :
    instructionSequenceAt 4266 false { bytes := bytes, pos := 2066, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 31, .end), { bytes := bytes, pos := 2887, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail19 :
    instructionSequenceAt 4278 false { bytes := bytes, pos := 1938, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := bytes, pos := 2887, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail5 :
    instructionSequenceAt 4292 false { bytes := bytes, pos := 1809, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 5, .end), { bytes := bytes, pos := 2887, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail0 :
    instructionSequenceAt 4297 false { bytes := bytes, pos := 1800, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 2887, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_36_t_tail0 :
    instructionSequenceAt 4233 false { bytes := bytes, pos := 3054, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody false)[36]!).childBody false).drop 0, .end), { bytes := bytes, pos := 3241, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_40_t_tail14 :
    instructionSequenceAt 4215 true { bytes := bytes, pos := 3279, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody false)[40]!).childBody false).drop 14, .end), { bytes := bytes, pos := 3408, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_40_t_tail0 :
    instructionSequenceAt 4229 true { bytes := bytes, pos := 3249, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody false)[40]!).childBody false).drop 0, .end), { bytes := bytes, pos := 3408, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_69_t_tail0 :
    instructionSequenceAt 4200 false { bytes := bytes, pos := 3511, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody false)[69]!).childBody false).drop 0, .end), { bytes := bytes, pos := 3806, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_tail0 :
    instructionSequenceAt 4175 false { bytes := bytes, pos := 3857, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false).drop 0, .end), { bytes := bytes, pos := 4668, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_4_t_tail0 :
    instructionSequenceAt 4265 false { bytes := bytes, pos := 4789, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody true)[4]!).childBody false).drop 0, .end), { bytes := bytes, pos := 5084, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_tail0 :
    instructionSequenceAt 4240 false { bytes := bytes, pos := 5135, limit := 6064 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false).drop 0, .end), { bytes := bytes, pos := 5946, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_tail0 :
    instructionSequenceAt 4299 false { bytes := bytes, pos := 1798, limit := 6064 } =
      .ok ((((((raw.core.codes[2]!).body)[27]!).childBody false).drop 0, .end), { bytes := bytes, pos := 2888, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_tail94 :
    instructionSequenceAt 4177 true { bytes := bytes, pos := 3855, limit := 6064 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody false).drop 94, .otherwise), { bytes := bytes, pos := 4779, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_tail69 :
    instructionSequenceAt 4202 true { bytes := bytes, pos := 3509, limit := 6064 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody false).drop 69, .otherwise), { bytes := bytes, pos := 4779, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_tail40 :
    instructionSequenceAt 4231 true { bytes := bytes, pos := 3247, limit := 6064 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody false).drop 40, .otherwise), { bytes := bytes, pos := 4779, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_tail36 :
    instructionSequenceAt 4235 true { bytes := bytes, pos := 3052, limit := 6064 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody false).drop 36, .otherwise), { bytes := bytes, pos := 4779, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_tail0 :
    instructionSequenceAt 4271 true { bytes := bytes, pos := 2972, limit := 6064 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody false).drop 0, .otherwise), { bytes := bytes, pos := 4779, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_tail29 :
    instructionSequenceAt 4242 false { bytes := bytes, pos := 5133, limit := 6064 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody true).drop 29, .end), { bytes := bytes, pos := 5983, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_tail4 :
    instructionSequenceAt 4267 false { bytes := bytes, pos := 4787, limit := 6064 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody true).drop 4, .end), { bytes := bytes, pos := 5983, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_tail0 :
    instructionSequenceAt 4271 false { bytes := bytes, pos := 4779, limit := 6064 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody true).drop 0, .end), { bytes := bytes, pos := 5983, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_tail55 :
    instructionSequenceAt 4273 false { bytes := bytes, pos := 2970, limit := 6064 } =
      .ok ((((raw.core.codes[2]!).body).drop 55, .end), { bytes := bytes, pos := 6064, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_tail27 :
    instructionSequenceAt 4301 false { bytes := bytes, pos := 1796, limit := 6064 } =
      .ok ((((raw.core.codes[2]!).body).drop 27, .end), { bytes := bytes, pos := 6064, limit := 6064 }) := by
  cbv

@[cbv_eval] theorem sequence_2_tail0 :
    instructionSequenceAt 4328 false { bytes := bytes, pos := 1736, limit := 6064 } =
      .ok ((((raw.core.codes[2]!).body).drop 0, .end), { bytes := bytes, pos := 6064, limit := 6064 }) := by
  cbv

theorem code2_decoded :
    code { bytes := bytes, pos := 1730, limit := 16469 } = .ok (raw.core.codes[2]!, { bytes := bytes, pos := 6064, limit := 16469 }) := by
  refine code_eq_of_parts (size := 4332)
    (payload := { bytes := bytes, pos := 1732, limit := 16469 })
    (bodyStart := { bytes := bytes, pos := 1736, limit := 6064 })
    (bodyFinish := { bytes := bytes, pos := 6064, limit := 6064 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_2_tail0
  · rfl

#print axioms code2_decoded

end Project.RunningSum.Artifact
