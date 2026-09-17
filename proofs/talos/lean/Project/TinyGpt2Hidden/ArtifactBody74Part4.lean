import Project.TinyGpt2Hidden.ArtifactBody74Part3

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail1560 : List Instr := ([Wasm.Binary.Instr.localSet 650,
 Wasm.Binary.Instr.i64Const 1140,
 Wasm.Binary.Instr.localSet 785,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 786,
 Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.localGet 786,
 Wasm.Binary.Instr.i64Add] ++ body74Tail1568)

@[cbv_eval] theorem sequence74_tail1560 :
    instructionSequenceAt 3616 false { bytes := artifactBytes, pos := 14135, limit := 15177 } =
      .ok ((body74Tail1560, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 650,
 Wasm.Binary.Instr.i64Const 1140,
 Wasm.Binary.Instr.localSet 785,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 786,
 Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.localGet 786,
 Wasm.Binary.Instr.i64Add] ++ body74Tail1568), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1552 : List Instr := ([Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 680,
 Wasm.Binary.Instr.localGet 613,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 649,
 Wasm.Binary.Instr.localGet 0] ++ body74Tail1560)

@[cbv_eval] theorem sequence74_tail1552 :
    instructionSequenceAt 3624 false { bytes := artifactBytes, pos := 14119, limit := 15177 } =
      .ok ((body74Tail1552, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 680,
 Wasm.Binary.Instr.localGet 613,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 649,
 Wasm.Binary.Instr.localGet 0] ++ body74Tail1560), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1544 : List Instr := ([Wasm.Binary.Instr.localGet 644,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 648,
 Wasm.Binary.Instr.localSet 647,
 Wasm.Binary.Instr.localSet 646,
 Wasm.Binary.Instr.localSet 645,
 Wasm.Binary.Instr.localGet 648,
 Wasm.Binary.Instr.f64ReinterpretI64] ++ body74Tail1552)

@[cbv_eval] theorem sequence74_tail1544 :
    instructionSequenceAt 3632 false { bytes := artifactBytes, pos := 14098, limit := 15177 } =
      .ok ((body74Tail1544, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 644,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 648,
 Wasm.Binary.Instr.localSet 647,
 Wasm.Binary.Instr.localSet 646,
 Wasm.Binary.Instr.localSet 645,
 Wasm.Binary.Instr.localGet 648,
 Wasm.Binary.Instr.f64ReinterpretI64] ++ body74Tail1552), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1536 : List Instr := ([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 642,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 643,
 Wasm.Binary.Instr.localGet 643,
 Wasm.Binary.Instr.localSet 644,
 Wasm.Binary.Instr.localGet 641,
 Wasm.Binary.Instr.localGet 642] ++ body74Tail1544)

@[cbv_eval] theorem sequence74_tail1536 :
    instructionSequenceAt 3640 false { bytes := artifactBytes, pos := 14076, limit := 15177 } =
      .ok ((body74Tail1536, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 642,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 643,
 Wasm.Binary.Instr.localGet 643,
 Wasm.Binary.Instr.localSet 644,
 Wasm.Binary.Instr.localGet 641,
 Wasm.Binary.Instr.localGet 642] ++ body74Tail1544), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1528 : List Instr := ([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 679,
 Wasm.Binary.Instr.localGet 520,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 641] ++ body74Tail1536)

@[cbv_eval] theorem sequence74_tail1528 :
    instructionSequenceAt 3648 false { bytes := artifactBytes, pos := 14061, limit := 15177 } =
      .ok ((body74Tail1528, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 679,
 Wasm.Binary.Instr.localGet 520,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 641] ++ body74Tail1536), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1520 : List Instr := ([Wasm.Binary.Instr.localGet 634,
 Wasm.Binary.Instr.localGet 636,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 640,
 Wasm.Binary.Instr.localSet 639,
 Wasm.Binary.Instr.localSet 638,
 Wasm.Binary.Instr.localSet 637,
 Wasm.Binary.Instr.localGet 639] ++ body74Tail1528)

@[cbv_eval] theorem sequence74_tail1520 :
    instructionSequenceAt 3656 false { bytes := artifactBytes, pos := 14038, limit := 15177 } =
      .ok ((body74Tail1520, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 634,
 Wasm.Binary.Instr.localGet 636,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 640,
 Wasm.Binary.Instr.localSet 639,
 Wasm.Binary.Instr.localSet 638,
 Wasm.Binary.Instr.localSet 637,
 Wasm.Binary.Instr.localGet 639] ++ body74Tail1528), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1512 : List Instr := ([Wasm.Binary.Instr.localSet 633,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 634,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 635,
 Wasm.Binary.Instr.localGet 635,
 Wasm.Binary.Instr.localSet 636,
 Wasm.Binary.Instr.localGet 633] ++ body74Tail1520)

@[cbv_eval] theorem sequence74_tail1512 :
    instructionSequenceAt 3664 false { bytes := artifactBytes, pos := 14016, limit := 15177 } =
      .ok ((body74Tail1512, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 633,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 634,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 635,
 Wasm.Binary.Instr.localGet 635,
 Wasm.Binary.Instr.localSet 636,
 Wasm.Binary.Instr.localGet 633] ++ body74Tail1520), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1504 : List Instr := ([Wasm.Binary.Instr.localGet 630,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 678,
 Wasm.Binary.Instr.localGet 519,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0] ++ body74Tail1512)

@[cbv_eval] theorem sequence74_tail1504 :
    instructionSequenceAt 3672 false { bytes := artifactBytes, pos := 14001, limit := 15177 } =
      .ok ((body74Tail1504, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 630,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 678,
 Wasm.Binary.Instr.localGet 519,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0] ++ body74Tail1512), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1496 : List Instr := ([Wasm.Binary.Instr.localGet 625,
 Wasm.Binary.Instr.localGet 626,
 Wasm.Binary.Instr.localGet 628,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 632,
 Wasm.Binary.Instr.localSet 631,
 Wasm.Binary.Instr.localSet 630,
 Wasm.Binary.Instr.localSet 629] ++ body74Tail1504)

@[cbv_eval] theorem sequence74_tail1496 :
    instructionSequenceAt 3680 false { bytes := artifactBytes, pos := 13978, limit := 15177 } =
      .ok ((body74Tail1496, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 625,
 Wasm.Binary.Instr.localGet 626,
 Wasm.Binary.Instr.localGet 628,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 632,
 Wasm.Binary.Instr.localSet 631,
 Wasm.Binary.Instr.localSet 630,
 Wasm.Binary.Instr.localSet 629] ++ body74Tail1504), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1488 : List Instr := ([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 625,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 626,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 627,
 Wasm.Binary.Instr.localGet 627,
 Wasm.Binary.Instr.localSet 628] ++ body74Tail1496)

@[cbv_eval] theorem sequence74_tail1488 :
    instructionSequenceAt 3688 false { bytes := artifactBytes, pos := 13957, limit := 15177 } =
      .ok ((body74Tail1488, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 625,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 626,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 627,
 Wasm.Binary.Instr.localGet 627,
 Wasm.Binary.Instr.localSet 628] ++ body74Tail1496), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1480 : List Instr := ([Wasm.Binary.Instr.localSet 621,
 Wasm.Binary.Instr.localGet 621,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 677,
 Wasm.Binary.Instr.localGet 518,
 Wasm.Binary.Instr.f64ReinterpretI64] ++ body74Tail1488)

@[cbv_eval] theorem sequence74_tail1480 :
    instructionSequenceAt 3696 false { bytes := artifactBytes, pos := 13941, limit := 15177 } =
      .ok ((body74Tail1480, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 621,
 Wasm.Binary.Instr.localGet 621,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 677,
 Wasm.Binary.Instr.localGet 518,
 Wasm.Binary.Instr.f64ReinterpretI64] ++ body74Tail1488), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1472 : List Instr := ([Wasm.Binary.Instr.localSet 620,
 Wasm.Binary.Instr.localGet 617,
 Wasm.Binary.Instr.localGet 618,
 Wasm.Binary.Instr.localGet 620,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 624,
 Wasm.Binary.Instr.localSet 623,
 Wasm.Binary.Instr.localSet 622] ++ body74Tail1480)

@[cbv_eval] theorem sequence74_tail1472 :
    instructionSequenceAt 3704 false { bytes := artifactBytes, pos := 13918, limit := 15177 } =
      .ok ((body74Tail1472, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 620,
 Wasm.Binary.Instr.localGet 617,
 Wasm.Binary.Instr.localGet 618,
 Wasm.Binary.Instr.localGet 620,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 624,
 Wasm.Binary.Instr.localSet 623,
 Wasm.Binary.Instr.localSet 622] ++ body74Tail1480), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1464 : List Instr := ([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 617,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 618,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 619,
 Wasm.Binary.Instr.localGet 619] ++ body74Tail1472)

@[cbv_eval] theorem sequence74_tail1464 :
    instructionSequenceAt 3712 false { bytes := artifactBytes, pos := 13899, limit := 15177 } =
      .ok ((body74Tail1464, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 617,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 618,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 619,
 Wasm.Binary.Instr.localGet 619] ++ body74Tail1472), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1456 : List Instr := ([Wasm.Binary.Instr.localGet 609,
 Wasm.Binary.Instr.localGet 610,
 Wasm.Binary.Instr.localGet 611,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 612,
 Wasm.Binary.Instr.localGet 612,
 Wasm.Binary.Instr.localSet 616,
 Wasm.Binary.Instr.localGet 517] ++ body74Tail1464)

@[cbv_eval] theorem sequence74_tail1456 :
    instructionSequenceAt 3720 false { bytes := artifactBytes, pos := 13876, limit := 15177 } =
      .ok ((body74Tail1456, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 609,
 Wasm.Binary.Instr.localGet 610,
 Wasm.Binary.Instr.localGet 611,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 612,
 Wasm.Binary.Instr.localGet 612,
 Wasm.Binary.Instr.localSet 616,
 Wasm.Binary.Instr.localGet 517] ++ body74Tail1464), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1448 : List Instr := ([Wasm.Binary.Instr.localGet 607,
 Wasm.Binary.Instr.localSet 611,
 Wasm.Binary.Instr.localGet 590,
 Wasm.Binary.Instr.localGet 591,
 Wasm.Binary.Instr.localGet 593,
 Wasm.Binary.Instr.localGet 594,
 Wasm.Binary.Instr.localGet 595,
 Wasm.Binary.Instr.localGet 608] ++ body74Tail1456)

@[cbv_eval] theorem sequence74_tail1448 :
    instructionSequenceAt 3728 false { bytes := artifactBytes, pos := 13852, limit := 15177 } =
      .ok ((body74Tail1448, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 607,
 Wasm.Binary.Instr.localSet 611,
 Wasm.Binary.Instr.localGet 590,
 Wasm.Binary.Instr.localGet 591,
 Wasm.Binary.Instr.localGet 593,
 Wasm.Binary.Instr.localGet 594,
 Wasm.Binary.Instr.localGet 595,
 Wasm.Binary.Instr.localGet 608] ++ body74Tail1456), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1440 : List Instr := ([Wasm.Binary.Instr.localSet 605,
 Wasm.Binary.Instr.localSet 604,
 Wasm.Binary.Instr.localGet 604,
 Wasm.Binary.Instr.localSet 608,
 Wasm.Binary.Instr.localGet 605,
 Wasm.Binary.Instr.localSet 609,
 Wasm.Binary.Instr.localGet 606,
 Wasm.Binary.Instr.localSet 610] ++ body74Tail1448)

@[cbv_eval] theorem sequence74_tail1440 :
    instructionSequenceAt 3736 false { bytes := artifactBytes, pos := 13828, limit := 15177 } =
      .ok ((body74Tail1440, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 605,
 Wasm.Binary.Instr.localSet 604,
 Wasm.Binary.Instr.localGet 604,
 Wasm.Binary.Instr.localSet 608,
 Wasm.Binary.Instr.localGet 605,
 Wasm.Binary.Instr.localSet 609,
 Wasm.Binary.Instr.localGet 606,
 Wasm.Binary.Instr.localSet 610] ++ body74Tail1448), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
