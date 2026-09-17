import Project.TinyGpt2Hidden.ArtifactBody74Part5

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail1304 : List Instr := ([Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 556,
 Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 557,
 Wasm.Binary.Instr.localGet 550,
 Wasm.Binary.Instr.localGet 551,
 Wasm.Binary.Instr.localGet 553,
 Wasm.Binary.Instr.localGet 554] ++ body74Tail1312)

@[cbv_eval] theorem sequence74_tail1304 :
    instructionSequenceAt 3872 false { bytes := artifactBytes, pos := 13441, limit := 15177 } =
      .ok ((body74Tail1304, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 556,
 Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 557,
 Wasm.Binary.Instr.localGet 550,
 Wasm.Binary.Instr.localGet 551,
 Wasm.Binary.Instr.localGet 553,
 Wasm.Binary.Instr.localGet 554] ++ body74Tail1312), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1296 : List Instr := ([Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 552,
 Wasm.Binary.Instr.localGet 552,
 Wasm.Binary.Instr.localSet 553,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 554,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 555] ++ body74Tail1304)

@[cbv_eval] theorem sequence74_tail1296 :
    instructionSequenceAt 3880 false { bytes := artifactBytes, pos := 13418, limit := 15177 } =
      .ok ((body74Tail1296, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 552,
 Wasm.Binary.Instr.localGet 552,
 Wasm.Binary.Instr.localSet 553,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 554,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 555] ++ body74Tail1304), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1288 : List Instr := ([Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 548,
 Wasm.Binary.Instr.i64Const 5,
 Wasm.Binary.Instr.localSet 549,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 550,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 551] ++ body74Tail1296)

@[cbv_eval] theorem sequence74_tail1288 :
    instructionSequenceAt 3888 false { bytes := artifactBytes, pos := 13398, limit := 15177 } =
      .ok ((body74Tail1288, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 548,
 Wasm.Binary.Instr.i64Const 5,
 Wasm.Binary.Instr.localSet 549,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 550,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 551] ++ body74Tail1296), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1280 : List Instr := ([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 544,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 545,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 546,
 Wasm.Binary.Instr.localGet 546,
 Wasm.Binary.Instr.localSet 547] ++ body74Tail1288)

@[cbv_eval] theorem sequence74_tail1280 :
    instructionSequenceAt 3896 false { bytes := artifactBytes, pos := 13377, limit := 15177 } =
      .ok ((body74Tail1280, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 544,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 545,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 546,
 Wasm.Binary.Instr.localGet 546,
 Wasm.Binary.Instr.localSet 547] ++ body74Tail1288), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1272 : List Instr := ([Wasm.Binary.Instr.localGet 539,
 Wasm.Binary.Instr.localGet 540,
 Wasm.Binary.Instr.localGet 541,
 Wasm.Binary.Instr.localGet 542,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 543,
 Wasm.Binary.Instr.localGet 543,
 Wasm.Binary.Instr.localSet 613] ++ body74Tail1280)

@[cbv_eval] theorem sequence74_tail1272 :
    instructionSequenceAt 3904 false { bytes := artifactBytes, pos := 13354, limit := 15177 } =
      .ok ((body74Tail1272, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 539,
 Wasm.Binary.Instr.localGet 540,
 Wasm.Binary.Instr.localGet 541,
 Wasm.Binary.Instr.localGet 542,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 543,
 Wasm.Binary.Instr.localGet 543,
 Wasm.Binary.Instr.localSet 613] ++ body74Tail1280), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1264 : List Instr := ([Wasm.Binary.Instr.localSet 541,
 Wasm.Binary.Instr.localGet 538,
 Wasm.Binary.Instr.localSet 542,
 Wasm.Binary.Instr.localGet 521,
 Wasm.Binary.Instr.localGet 522,
 Wasm.Binary.Instr.localGet 524,
 Wasm.Binary.Instr.localGet 525,
 Wasm.Binary.Instr.localGet 526] ++ body74Tail1272)

@[cbv_eval] theorem sequence74_tail1264 :
    instructionSequenceAt 3912 false { bytes := artifactBytes, pos := 13330, limit := 15177 } =
      .ok ((body74Tail1264, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 541,
 Wasm.Binary.Instr.localGet 538,
 Wasm.Binary.Instr.localSet 542,
 Wasm.Binary.Instr.localGet 521,
 Wasm.Binary.Instr.localGet 522,
 Wasm.Binary.Instr.localGet 524,
 Wasm.Binary.Instr.localGet 525,
 Wasm.Binary.Instr.localGet 526] ++ body74Tail1272), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1256 : List Instr := ([Wasm.Binary.Instr.localSet 537,
 Wasm.Binary.Instr.localSet 536,
 Wasm.Binary.Instr.localSet 535,
 Wasm.Binary.Instr.localGet 535,
 Wasm.Binary.Instr.localSet 539,
 Wasm.Binary.Instr.localGet 536,
 Wasm.Binary.Instr.localSet 540,
 Wasm.Binary.Instr.localGet 537] ++ body74Tail1264)

@[cbv_eval] theorem sequence74_tail1256 :
    instructionSequenceAt 3920 false { bytes := artifactBytes, pos := 13306, limit := 15177 } =
      .ok ((body74Tail1256, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 537,
 Wasm.Binary.Instr.localSet 536,
 Wasm.Binary.Instr.localSet 535,
 Wasm.Binary.Instr.localGet 535,
 Wasm.Binary.Instr.localSet 539,
 Wasm.Binary.Instr.localGet 536,
 Wasm.Binary.Instr.localSet 540,
 Wasm.Binary.Instr.localGet 537] ++ body74Tail1264), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1248 : List Instr := ([Wasm.Binary.Instr.localGet 528,
 Wasm.Binary.Instr.localGet 530,
 Wasm.Binary.Instr.localGet 531,
 Wasm.Binary.Instr.localGet 532,
 Wasm.Binary.Instr.localGet 533,
 Wasm.Binary.Instr.localGet 534,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 538] ++ body74Tail1256)

@[cbv_eval] theorem sequence74_tail1248 :
    instructionSequenceAt 3928 false { bytes := artifactBytes, pos := 13283, limit := 15177 } =
      .ok ((body74Tail1248, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 528,
 Wasm.Binary.Instr.localGet 530,
 Wasm.Binary.Instr.localGet 531,
 Wasm.Binary.Instr.localGet 532,
 Wasm.Binary.Instr.localGet 533,
 Wasm.Binary.Instr.localGet 534,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 538] ++ body74Tail1256), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1240 : List Instr := ([Wasm.Binary.Instr.localSet 531,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 532,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 533,
 Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 534,
 Wasm.Binary.Instr.localGet 527] ++ body74Tail1248)

@[cbv_eval] theorem sequence74_tail1240 :
    instructionSequenceAt 3936 false { bytes := artifactBytes, pos := 13259, limit := 15177 } =
      .ok ((body74Tail1240, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 531,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 532,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 533,
 Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 534,
 Wasm.Binary.Instr.localGet 527] ++ body74Tail1248), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1232 : List Instr := ([Wasm.Binary.Instr.localSet 527,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 528,
 Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 529,
 Wasm.Binary.Instr.localGet 529,
 Wasm.Binary.Instr.localSet 530,
 Wasm.Binary.Instr.localGet 421] ++ body74Tail1240)

@[cbv_eval] theorem sequence74_tail1232 :
    instructionSequenceAt 3944 false { bytes := artifactBytes, pos := 13237, limit := 15177 } =
      .ok ((body74Tail1232, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 527,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 528,
 Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 529,
 Wasm.Binary.Instr.localGet 529,
 Wasm.Binary.Instr.localSet 530,
 Wasm.Binary.Instr.localGet 421] ++ body74Tail1240), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1224 : List Instr := ([Wasm.Binary.Instr.localSet 523,
 Wasm.Binary.Instr.localGet 523,
 Wasm.Binary.Instr.localSet 524,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 525,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 526,
 Wasm.Binary.Instr.i64Const 0] ++ body74Tail1232)

@[cbv_eval] theorem sequence74_tail1224 :
    instructionSequenceAt 3952 false { bytes := artifactBytes, pos := 13216, limit := 15177 } =
      .ok ((body74Tail1224, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 523,
 Wasm.Binary.Instr.localGet 523,
 Wasm.Binary.Instr.localSet 524,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 525,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 526,
 Wasm.Binary.Instr.i64Const 0] ++ body74Tail1232), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1216 : List Instr := ([Wasm.Binary.Instr.localSet 516,
 Wasm.Binary.Instr.localGet 516,
 Wasm.Binary.Instr.localSet 520,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 521,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 522,
 Wasm.Binary.Instr.call 55] ++ body74Tail1224)

@[cbv_eval] theorem sequence74_tail1216 :
    instructionSequenceAt 3960 false { bytes := artifactBytes, pos := 13195, limit := 15177 } =
      .ok ((body74Tail1216, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 516,
 Wasm.Binary.Instr.localGet 516,
 Wasm.Binary.Instr.localSet 520,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 521,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 522,
 Wasm.Binary.Instr.call 55] ++ body74Tail1224), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1208 : List Instr := ([Wasm.Binary.Instr.localGet 497,
 Wasm.Binary.Instr.localGet 498,
 Wasm.Binary.Instr.localGet 499,
 Wasm.Binary.Instr.localGet 512,
 Wasm.Binary.Instr.localGet 513,
 Wasm.Binary.Instr.localGet 514,
 Wasm.Binary.Instr.localGet 515,
 Wasm.Binary.Instr.call 25] ++ body74Tail1216)

@[cbv_eval] theorem sequence74_tail1208 :
    instructionSequenceAt 3968 false { bytes := artifactBytes, pos := 13172, limit := 15177 } =
      .ok ((body74Tail1208, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 497,
 Wasm.Binary.Instr.localGet 498,
 Wasm.Binary.Instr.localGet 499,
 Wasm.Binary.Instr.localGet 512,
 Wasm.Binary.Instr.localGet 513,
 Wasm.Binary.Instr.localGet 514,
 Wasm.Binary.Instr.localGet 515,
 Wasm.Binary.Instr.call 25] ++ body74Tail1216), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1200 : List Instr := ([Wasm.Binary.Instr.localGet 509,
 Wasm.Binary.Instr.localSet 513,
 Wasm.Binary.Instr.localGet 510,
 Wasm.Binary.Instr.localSet 514,
 Wasm.Binary.Instr.localGet 511,
 Wasm.Binary.Instr.localSet 515,
 Wasm.Binary.Instr.localGet 494,
 Wasm.Binary.Instr.localGet 495] ++ body74Tail1208)

@[cbv_eval] theorem sequence74_tail1200 :
    instructionSequenceAt 3976 false { bytes := artifactBytes, pos := 13148, limit := 15177 } =
      .ok ((body74Tail1200, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 509,
 Wasm.Binary.Instr.localSet 513,
 Wasm.Binary.Instr.localGet 510,
 Wasm.Binary.Instr.localSet 514,
 Wasm.Binary.Instr.localGet 511,
 Wasm.Binary.Instr.localSet 515,
 Wasm.Binary.Instr.localGet 494,
 Wasm.Binary.Instr.localGet 495] ++ body74Tail1208), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1192 : List Instr := ([Wasm.Binary.Instr.localGet 507,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 511,
 Wasm.Binary.Instr.localSet 510,
 Wasm.Binary.Instr.localSet 509,
 Wasm.Binary.Instr.localSet 508,
 Wasm.Binary.Instr.localGet 508,
 Wasm.Binary.Instr.localSet 512] ++ body74Tail1200)

@[cbv_eval] theorem sequence74_tail1192 :
    instructionSequenceAt 3984 false { bytes := artifactBytes, pos := 13125, limit := 15177 } =
      .ok ((body74Tail1192, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 507,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 511,
 Wasm.Binary.Instr.localSet 510,
 Wasm.Binary.Instr.localSet 509,
 Wasm.Binary.Instr.localSet 508,
 Wasm.Binary.Instr.localGet 508,
 Wasm.Binary.Instr.localSet 512] ++ body74Tail1200), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1184 : List Instr := ([Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 507,
 Wasm.Binary.Instr.localGet 500,
 Wasm.Binary.Instr.localGet 501,
 Wasm.Binary.Instr.localGet 503,
 Wasm.Binary.Instr.localGet 504,
 Wasm.Binary.Instr.localGet 505,
 Wasm.Binary.Instr.localGet 506] ++ body74Tail1192)

@[cbv_eval] theorem sequence74_tail1184 :
    instructionSequenceAt 3992 false { bytes := artifactBytes, pos := 13101, limit := 15177 } =
      .ok ((body74Tail1184, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 507,
 Wasm.Binary.Instr.localGet 500,
 Wasm.Binary.Instr.localGet 501,
 Wasm.Binary.Instr.localGet 503,
 Wasm.Binary.Instr.localGet 504,
 Wasm.Binary.Instr.localGet 505,
 Wasm.Binary.Instr.localGet 506] ++ body74Tail1192), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
