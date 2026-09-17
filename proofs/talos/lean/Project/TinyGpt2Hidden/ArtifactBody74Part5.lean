import Project.TinyGpt2Hidden.ArtifactBody74Part4

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail1432 : List Instr := ([Wasm.Binary.Instr.localGet 599,
 Wasm.Binary.Instr.localGet 600,
 Wasm.Binary.Instr.localGet 601,
 Wasm.Binary.Instr.localGet 602,
 Wasm.Binary.Instr.localGet 603,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 607,
 Wasm.Binary.Instr.localSet 606] ++ body74Tail1440)

@[cbv_eval] theorem sequence74_tail1432 :
    instructionSequenceAt 3744 false { bytes := artifactBytes, pos := 13805, limit := 15177 } =
      .ok ((body74Tail1432, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 599,
 Wasm.Binary.Instr.localGet 600,
 Wasm.Binary.Instr.localGet 601,
 Wasm.Binary.Instr.localGet 602,
 Wasm.Binary.Instr.localGet 603,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 607,
 Wasm.Binary.Instr.localSet 606] ++ body74Tail1440), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1424 : List Instr := ([Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 601,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 602,
 Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 603,
 Wasm.Binary.Instr.localGet 596,
 Wasm.Binary.Instr.localGet 597] ++ body74Tail1432)

@[cbv_eval] theorem sequence74_tail1424 :
    instructionSequenceAt 3752 false { bytes := artifactBytes, pos := 13781, limit := 15177 } =
      .ok ((body74Tail1424, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 601,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 602,
 Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 603,
 Wasm.Binary.Instr.localGet 596,
 Wasm.Binary.Instr.localGet 597] ++ body74Tail1432), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1416 : List Instr := ([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 597,
 Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 598,
 Wasm.Binary.Instr.localGet 598,
 Wasm.Binary.Instr.localSet 599,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 600] ++ body74Tail1424)

@[cbv_eval] theorem sequence74_tail1416 :
    instructionSequenceAt 3760 false { bytes := artifactBytes, pos := 13759, limit := 15177 } =
      .ok ((body74Tail1416, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 597,
 Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 598,
 Wasm.Binary.Instr.localGet 598,
 Wasm.Binary.Instr.localSet 599,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 600] ++ body74Tail1424), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1408 : List Instr := ([Wasm.Binary.Instr.localGet 592,
 Wasm.Binary.Instr.localSet 593,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 594,
 Wasm.Binary.Instr.i64Const 7,
 Wasm.Binary.Instr.localSet 595,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 596] ++ body74Tail1416)

@[cbv_eval] theorem sequence74_tail1408 :
    instructionSequenceAt 3768 false { bytes := artifactBytes, pos := 13738, limit := 15177 } =
      .ok ((body74Tail1408, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 592,
 Wasm.Binary.Instr.localSet 593,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 594,
 Wasm.Binary.Instr.i64Const 7,
 Wasm.Binary.Instr.localSet 595,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 596] ++ body74Tail1416), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1400 : List Instr := ([Wasm.Binary.Instr.localGet 589,
 Wasm.Binary.Instr.localSet 615,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 590,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 591,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 592] ++ body74Tail1408)

@[cbv_eval] theorem sequence74_tail1400 :
    instructionSequenceAt 3776 false { bytes := artifactBytes, pos := 13717, limit := 15177 } =
      .ok ((body74Tail1400, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 589,
 Wasm.Binary.Instr.localSet 615,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 590,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 591,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 592] ++ body74Tail1408), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1392 : List Instr := ([Wasm.Binary.Instr.localGet 571,
 Wasm.Binary.Instr.localGet 572,
 Wasm.Binary.Instr.localGet 585,
 Wasm.Binary.Instr.localGet 586,
 Wasm.Binary.Instr.localGet 587,
 Wasm.Binary.Instr.localGet 588,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 589] ++ body74Tail1400)

@[cbv_eval] theorem sequence74_tail1392 :
    instructionSequenceAt 3784 false { bytes := artifactBytes, pos := 13694, limit := 15177 } =
      .ok ((body74Tail1392, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 571,
 Wasm.Binary.Instr.localGet 572,
 Wasm.Binary.Instr.localGet 585,
 Wasm.Binary.Instr.localGet 586,
 Wasm.Binary.Instr.localGet 587,
 Wasm.Binary.Instr.localGet 588,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 589] ++ body74Tail1400), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1384 : List Instr := ([Wasm.Binary.Instr.localSet 586,
 Wasm.Binary.Instr.localGet 583,
 Wasm.Binary.Instr.localSet 587,
 Wasm.Binary.Instr.localGet 584,
 Wasm.Binary.Instr.localSet 588,
 Wasm.Binary.Instr.localGet 567,
 Wasm.Binary.Instr.localGet 568,
 Wasm.Binary.Instr.localGet 570] ++ body74Tail1392)

@[cbv_eval] theorem sequence74_tail1384 :
    instructionSequenceAt 3792 false { bytes := artifactBytes, pos := 13670, limit := 15177 } =
      .ok ((body74Tail1384, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 586,
 Wasm.Binary.Instr.localGet 583,
 Wasm.Binary.Instr.localSet 587,
 Wasm.Binary.Instr.localGet 584,
 Wasm.Binary.Instr.localSet 588,
 Wasm.Binary.Instr.localGet 567,
 Wasm.Binary.Instr.localGet 568,
 Wasm.Binary.Instr.localGet 570] ++ body74Tail1392), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1376 : List Instr := ([Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 584,
 Wasm.Binary.Instr.localSet 583,
 Wasm.Binary.Instr.localSet 582,
 Wasm.Binary.Instr.localSet 581,
 Wasm.Binary.Instr.localGet 581,
 Wasm.Binary.Instr.localSet 585,
 Wasm.Binary.Instr.localGet 582] ++ body74Tail1384)

@[cbv_eval] theorem sequence74_tail1376 :
    instructionSequenceAt 3800 false { bytes := artifactBytes, pos := 13647, limit := 15177 } =
      .ok ((body74Tail1376, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 584,
 Wasm.Binary.Instr.localSet 583,
 Wasm.Binary.Instr.localSet 582,
 Wasm.Binary.Instr.localSet 581,
 Wasm.Binary.Instr.localGet 581,
 Wasm.Binary.Instr.localSet 585,
 Wasm.Binary.Instr.localGet 582] ++ body74Tail1384), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1368 : List Instr := ([Wasm.Binary.Instr.localSet 580,
 Wasm.Binary.Instr.localGet 573,
 Wasm.Binary.Instr.localGet 574,
 Wasm.Binary.Instr.localGet 576,
 Wasm.Binary.Instr.localGet 577,
 Wasm.Binary.Instr.localGet 578,
 Wasm.Binary.Instr.localGet 579,
 Wasm.Binary.Instr.localGet 580] ++ body74Tail1376)

@[cbv_eval] theorem sequence74_tail1368 :
    instructionSequenceAt 3808 false { bytes := artifactBytes, pos := 13623, limit := 15177 } =
      .ok ((body74Tail1368, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 580,
 Wasm.Binary.Instr.localGet 573,
 Wasm.Binary.Instr.localGet 574,
 Wasm.Binary.Instr.localGet 576,
 Wasm.Binary.Instr.localGet 577,
 Wasm.Binary.Instr.localGet 578,
 Wasm.Binary.Instr.localGet 579,
 Wasm.Binary.Instr.localGet 580] ++ body74Tail1376), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1360 : List Instr := ([Wasm.Binary.Instr.localSet 576,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 577,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 578,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 579,
 Wasm.Binary.Instr.localGet 424] ++ body74Tail1368)

@[cbv_eval] theorem sequence74_tail1360 :
    instructionSequenceAt 3816 false { bytes := artifactBytes, pos := 13599, limit := 15177 } =
      .ok ((body74Tail1360, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 576,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 577,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 578,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.localSet 579,
 Wasm.Binary.Instr.localGet 424] ++ body74Tail1368), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1352 : List Instr := ([Wasm.Binary.Instr.localSet 572,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 573,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 574,
 Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 575,
 Wasm.Binary.Instr.localGet 575] ++ body74Tail1360)

@[cbv_eval] theorem sequence74_tail1352 :
    instructionSequenceAt 3824 false { bytes := artifactBytes, pos := 13578, limit := 15177 } =
      .ok ((body74Tail1352, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 572,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 573,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 574,
 Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 575,
 Wasm.Binary.Instr.localGet 575] ++ body74Tail1360), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1344 : List Instr := ([Wasm.Binary.Instr.localSet 568,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 569,
 Wasm.Binary.Instr.localGet 569,
 Wasm.Binary.Instr.localSet 570,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 571,
 Wasm.Binary.Instr.i64Const 6] ++ body74Tail1352)

@[cbv_eval] theorem sequence74_tail1344 :
    instructionSequenceAt 3832 false { bytes := artifactBytes, pos := 13557, limit := 15177 } =
      .ok ((body74Tail1344, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 568,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 569,
 Wasm.Binary.Instr.localGet 569,
 Wasm.Binary.Instr.localSet 570,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 571,
 Wasm.Binary.Instr.i64Const 6] ++ body74Tail1352), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1336 : List Instr := ([Wasm.Binary.Instr.localGet 565,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 566,
 Wasm.Binary.Instr.localGet 566,
 Wasm.Binary.Instr.localSet 614,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 567,
 Wasm.Binary.Instr.localGet 0] ++ body74Tail1344)

@[cbv_eval] theorem sequence74_tail1336 :
    instructionSequenceAt 3840 false { bytes := artifactBytes, pos := 13536, limit := 15177 } =
      .ok ((body74Tail1336, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 565,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 566,
 Wasm.Binary.Instr.localGet 566,
 Wasm.Binary.Instr.localSet 614,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 567,
 Wasm.Binary.Instr.localGet 0] ++ body74Tail1344), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1328 : List Instr := ([Wasm.Binary.Instr.localGet 544,
 Wasm.Binary.Instr.localGet 545,
 Wasm.Binary.Instr.localGet 547,
 Wasm.Binary.Instr.localGet 548,
 Wasm.Binary.Instr.localGet 549,
 Wasm.Binary.Instr.localGet 562,
 Wasm.Binary.Instr.localGet 563,
 Wasm.Binary.Instr.localGet 564] ++ body74Tail1336)

@[cbv_eval] theorem sequence74_tail1328 :
    instructionSequenceAt 3848 false { bytes := artifactBytes, pos := 13512, limit := 15177 } =
      .ok ((body74Tail1328, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 544,
 Wasm.Binary.Instr.localGet 545,
 Wasm.Binary.Instr.localGet 547,
 Wasm.Binary.Instr.localGet 548,
 Wasm.Binary.Instr.localGet 549,
 Wasm.Binary.Instr.localGet 562,
 Wasm.Binary.Instr.localGet 563,
 Wasm.Binary.Instr.localGet 564] ++ body74Tail1336), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1320 : List Instr := ([Wasm.Binary.Instr.localGet 558,
 Wasm.Binary.Instr.localSet 562,
 Wasm.Binary.Instr.localGet 559,
 Wasm.Binary.Instr.localSet 563,
 Wasm.Binary.Instr.localGet 560,
 Wasm.Binary.Instr.localSet 564,
 Wasm.Binary.Instr.localGet 561,
 Wasm.Binary.Instr.localSet 565] ++ body74Tail1328)

@[cbv_eval] theorem sequence74_tail1320 :
    instructionSequenceAt 3856 false { bytes := artifactBytes, pos := 13488, limit := 15177 } =
      .ok ((body74Tail1320, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 558,
 Wasm.Binary.Instr.localSet 562,
 Wasm.Binary.Instr.localGet 559,
 Wasm.Binary.Instr.localSet 563,
 Wasm.Binary.Instr.localGet 560,
 Wasm.Binary.Instr.localSet 564,
 Wasm.Binary.Instr.localGet 561,
 Wasm.Binary.Instr.localSet 565] ++ body74Tail1328), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1312 : List Instr := ([Wasm.Binary.Instr.localGet 555,
 Wasm.Binary.Instr.localGet 556,
 Wasm.Binary.Instr.localGet 557,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 561,
 Wasm.Binary.Instr.localSet 560,
 Wasm.Binary.Instr.localSet 559,
 Wasm.Binary.Instr.localSet 558] ++ body74Tail1320)

@[cbv_eval] theorem sequence74_tail1312 :
    instructionSequenceAt 3864 false { bytes := artifactBytes, pos := 13465, limit := 15177 } =
      .ok ((body74Tail1312, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 555,
 Wasm.Binary.Instr.localGet 556,
 Wasm.Binary.Instr.localGet 557,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 561,
 Wasm.Binary.Instr.localSet 560,
 Wasm.Binary.Instr.localSet 559,
 Wasm.Binary.Instr.localSet 558] ++ body74Tail1320), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
