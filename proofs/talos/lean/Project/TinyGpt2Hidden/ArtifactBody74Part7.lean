import Project.TinyGpt2Hidden.ArtifactBody74Part6

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail1176 : List Instr := ([Wasm.Binary.Instr.localGet 502,
 Wasm.Binary.Instr.localSet 503,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 504,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 505,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 506] ++ body74Tail1184)

@[cbv_eval] theorem sequence74_tail1176 :
    instructionSequenceAt 4000 false { bytes := artifactBytes, pos := 13077, limit := 15177 } =
      .ok ((body74Tail1176, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 502,
 Wasm.Binary.Instr.localSet 503,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 504,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 505,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 506] ++ body74Tail1184), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1168 : List Instr := ([Wasm.Binary.Instr.i64Const 3,
 Wasm.Binary.Instr.localSet 499,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 500,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 501,
 Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 502] ++ body74Tail1176)

@[cbv_eval] theorem sequence74_tail1168 :
    instructionSequenceAt 4008 false { bytes := artifactBytes, pos := 13057, limit := 15177 } =
      .ok ((body74Tail1168, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 3,
 Wasm.Binary.Instr.localSet 499,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 500,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 501,
 Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 502] ++ body74Tail1176), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1160 : List Instr := ([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 495,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 496,
 Wasm.Binary.Instr.localGet 496,
 Wasm.Binary.Instr.localSet 497,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 498] ++ body74Tail1168)

@[cbv_eval] theorem sequence74_tail1160 :
    instructionSequenceAt 4016 false { bytes := artifactBytes, pos := 13036, limit := 15177 } =
      .ok ((body74Tail1160, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 495,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 496,
 Wasm.Binary.Instr.localGet 496,
 Wasm.Binary.Instr.localSet 497,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 498] ++ body74Tail1168), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1152 : List Instr := ([Wasm.Binary.Instr.localGet 491,
 Wasm.Binary.Instr.localGet 492,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 493,
 Wasm.Binary.Instr.localGet 493,
 Wasm.Binary.Instr.localSet 519,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 494] ++ body74Tail1160)

@[cbv_eval] theorem sequence74_tail1152 :
    instructionSequenceAt 4024 false { bytes := artifactBytes, pos := 13014, limit := 15177 } =
      .ok ((body74Tail1152, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 491,
 Wasm.Binary.Instr.localGet 492,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 493,
 Wasm.Binary.Instr.localGet 493,
 Wasm.Binary.Instr.localSet 519,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 494] ++ body74Tail1160), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1144 : List Instr := ([Wasm.Binary.Instr.localSet 492,
 Wasm.Binary.Instr.localGet 471,
 Wasm.Binary.Instr.localGet 472,
 Wasm.Binary.Instr.localGet 474,
 Wasm.Binary.Instr.localGet 475,
 Wasm.Binary.Instr.localGet 476,
 Wasm.Binary.Instr.localGet 489,
 Wasm.Binary.Instr.localGet 490] ++ body74Tail1152)

@[cbv_eval] theorem sequence74_tail1144 :
    instructionSequenceAt 4032 false { bytes := artifactBytes, pos := 12990, limit := 15177 } =
      .ok ((body74Tail1144, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 492,
 Wasm.Binary.Instr.localGet 471,
 Wasm.Binary.Instr.localGet 472,
 Wasm.Binary.Instr.localGet 474,
 Wasm.Binary.Instr.localGet 475,
 Wasm.Binary.Instr.localGet 476,
 Wasm.Binary.Instr.localGet 489,
 Wasm.Binary.Instr.localGet 490] ++ body74Tail1152), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1136 : List Instr := ([Wasm.Binary.Instr.localSet 485,
 Wasm.Binary.Instr.localGet 485,
 Wasm.Binary.Instr.localSet 489,
 Wasm.Binary.Instr.localGet 486,
 Wasm.Binary.Instr.localSet 490,
 Wasm.Binary.Instr.localGet 487,
 Wasm.Binary.Instr.localSet 491,
 Wasm.Binary.Instr.localGet 488] ++ body74Tail1144)

@[cbv_eval] theorem sequence74_tail1136 :
    instructionSequenceAt 4040 false { bytes := artifactBytes, pos := 12966, limit := 15177 } =
      .ok ((body74Tail1136, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 485,
 Wasm.Binary.Instr.localGet 485,
 Wasm.Binary.Instr.localSet 489,
 Wasm.Binary.Instr.localGet 486,
 Wasm.Binary.Instr.localSet 490,
 Wasm.Binary.Instr.localGet 487,
 Wasm.Binary.Instr.localSet 491,
 Wasm.Binary.Instr.localGet 488] ++ body74Tail1144), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1128 : List Instr := ([Wasm.Binary.Instr.localGet 481,
 Wasm.Binary.Instr.localGet 482,
 Wasm.Binary.Instr.localGet 483,
 Wasm.Binary.Instr.localGet 484,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 488,
 Wasm.Binary.Instr.localSet 487,
 Wasm.Binary.Instr.localSet 486] ++ body74Tail1136)

@[cbv_eval] theorem sequence74_tail1128 :
    instructionSequenceAt 4048 false { bytes := artifactBytes, pos := 12943, limit := 15177 } =
      .ok ((body74Tail1128, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 481,
 Wasm.Binary.Instr.localGet 482,
 Wasm.Binary.Instr.localGet 483,
 Wasm.Binary.Instr.localGet 484,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 488,
 Wasm.Binary.Instr.localSet 487,
 Wasm.Binary.Instr.localSet 486] ++ body74Tail1136), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1120 : List Instr := ([Wasm.Binary.Instr.localSet 482,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 483,
 Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 484,
 Wasm.Binary.Instr.localGet 477,
 Wasm.Binary.Instr.localGet 478,
 Wasm.Binary.Instr.localGet 480] ++ body74Tail1128)

@[cbv_eval] theorem sequence74_tail1120 :
    instructionSequenceAt 4056 false { bytes := artifactBytes, pos := 12919, limit := 15177 } =
      .ok ((body74Tail1120, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 482,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 483,
 Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 484,
 Wasm.Binary.Instr.localGet 477,
 Wasm.Binary.Instr.localGet 478,
 Wasm.Binary.Instr.localGet 480] ++ body74Tail1128), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1112 : List Instr := ([Wasm.Binary.Instr.localSet 478,
 Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 479,
 Wasm.Binary.Instr.localGet 479,
 Wasm.Binary.Instr.localSet 480,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 481,
 Wasm.Binary.Instr.localGet 422] ++ body74Tail1120)

@[cbv_eval] theorem sequence74_tail1112 :
    instructionSequenceAt 4064 false { bytes := artifactBytes, pos := 12896, limit := 15177 } =
      .ok ((body74Tail1112, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 478,
 Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 479,
 Wasm.Binary.Instr.localGet 479,
 Wasm.Binary.Instr.localSet 480,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 481,
 Wasm.Binary.Instr.localGet 422] ++ body74Tail1120), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1104 : List Instr := ([Wasm.Binary.Instr.localSet 474,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 475,
 Wasm.Binary.Instr.i64Const 2,
 Wasm.Binary.Instr.localSet 476,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 477,
 Wasm.Binary.Instr.localGet 0] ++ body74Tail1112)

@[cbv_eval] theorem sequence74_tail1104 :
    instructionSequenceAt 4072 false { bytes := artifactBytes, pos := 12876, limit := 15177 } =
      .ok ((body74Tail1104, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 474,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 475,
 Wasm.Binary.Instr.i64Const 2,
 Wasm.Binary.Instr.localSet 476,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 477,
 Wasm.Binary.Instr.localGet 0] ++ body74Tail1112), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1096 : List Instr := ([Wasm.Binary.Instr.localSet 518,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 471,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 472,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 473,
 Wasm.Binary.Instr.localGet 473] ++ body74Tail1104)

@[cbv_eval] theorem sequence74_tail1096 :
    instructionSequenceAt 4080 false { bytes := artifactBytes, pos := 12855, limit := 15177 } =
      .ok ((body74Tail1096, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 518,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 471,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 472,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 473,
 Wasm.Binary.Instr.localGet 473] ++ body74Tail1104), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1088 : List Instr := ([Wasm.Binary.Instr.localGet 453,
 Wasm.Binary.Instr.localGet 466,
 Wasm.Binary.Instr.localGet 467,
 Wasm.Binary.Instr.localGet 468,
 Wasm.Binary.Instr.localGet 469,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 470,
 Wasm.Binary.Instr.localGet 470] ++ body74Tail1096)

@[cbv_eval] theorem sequence74_tail1088 :
    instructionSequenceAt 4088 false { bytes := artifactBytes, pos := 12832, limit := 15177 } =
      .ok ((body74Tail1088, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 453,
 Wasm.Binary.Instr.localGet 466,
 Wasm.Binary.Instr.localGet 467,
 Wasm.Binary.Instr.localGet 468,
 Wasm.Binary.Instr.localGet 469,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 470,
 Wasm.Binary.Instr.localGet 470] ++ body74Tail1096), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1080 : List Instr := ([Wasm.Binary.Instr.localGet 464,
 Wasm.Binary.Instr.localSet 468,
 Wasm.Binary.Instr.localGet 465,
 Wasm.Binary.Instr.localSet 469,
 Wasm.Binary.Instr.localGet 448,
 Wasm.Binary.Instr.localGet 449,
 Wasm.Binary.Instr.localGet 451,
 Wasm.Binary.Instr.localGet 452] ++ body74Tail1088)

@[cbv_eval] theorem sequence74_tail1080 :
    instructionSequenceAt 4096 false { bytes := artifactBytes, pos := 12808, limit := 15177 } =
      .ok ((body74Tail1080, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 464,
 Wasm.Binary.Instr.localSet 468,
 Wasm.Binary.Instr.localGet 465,
 Wasm.Binary.Instr.localSet 469,
 Wasm.Binary.Instr.localGet 448,
 Wasm.Binary.Instr.localGet 449,
 Wasm.Binary.Instr.localGet 451,
 Wasm.Binary.Instr.localGet 452] ++ body74Tail1088), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1072 : List Instr := ([Wasm.Binary.Instr.localSet 465,
 Wasm.Binary.Instr.localSet 464,
 Wasm.Binary.Instr.localSet 463,
 Wasm.Binary.Instr.localSet 462,
 Wasm.Binary.Instr.localGet 462,
 Wasm.Binary.Instr.localSet 466,
 Wasm.Binary.Instr.localGet 463,
 Wasm.Binary.Instr.localSet 467] ++ body74Tail1080)

@[cbv_eval] theorem sequence74_tail1072 :
    instructionSequenceAt 4104 false { bytes := artifactBytes, pos := 12784, limit := 15177 } =
      .ok ((body74Tail1072, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 465,
 Wasm.Binary.Instr.localSet 464,
 Wasm.Binary.Instr.localSet 463,
 Wasm.Binary.Instr.localSet 462,
 Wasm.Binary.Instr.localGet 462,
 Wasm.Binary.Instr.localSet 466,
 Wasm.Binary.Instr.localGet 463,
 Wasm.Binary.Instr.localSet 467] ++ body74Tail1080), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1064 : List Instr := ([Wasm.Binary.Instr.localGet 454,
 Wasm.Binary.Instr.localGet 455,
 Wasm.Binary.Instr.localGet 457,
 Wasm.Binary.Instr.localGet 458,
 Wasm.Binary.Instr.localGet 459,
 Wasm.Binary.Instr.localGet 460,
 Wasm.Binary.Instr.localGet 461,
 Wasm.Binary.Instr.call 17] ++ body74Tail1072)

@[cbv_eval] theorem sequence74_tail1064 :
    instructionSequenceAt 4112 false { bytes := artifactBytes, pos := 12761, limit := 15177 } =
      .ok ((body74Tail1064, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 454,
 Wasm.Binary.Instr.localGet 455,
 Wasm.Binary.Instr.localGet 457,
 Wasm.Binary.Instr.localGet 458,
 Wasm.Binary.Instr.localGet 459,
 Wasm.Binary.Instr.localGet 460,
 Wasm.Binary.Instr.localGet 461,
 Wasm.Binary.Instr.call 17] ++ body74Tail1072), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1056 : List Instr := ([Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 458,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 459,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 460,
 Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 461] ++ body74Tail1064)

@[cbv_eval] theorem sequence74_tail1056 :
    instructionSequenceAt 4120 false { bytes := artifactBytes, pos := 12737, limit := 15177 } =
      .ok ((body74Tail1056, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 458,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 459,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 460,
 Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 461] ++ body74Tail1064), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
