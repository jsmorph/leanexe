import Project.TinyGpt2Hidden.ArtifactBody74Part2

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail1688 : List Instr := ([Wasm.Binary.Instr.localGet 686,
 Wasm.Binary.Instr.localGet 687,
 Wasm.Binary.Instr.localGet 688,
 Wasm.Binary.Instr.call 65,
 Wasm.Binary.Instr.localSet 692,
 Wasm.Binary.Instr.localSet 691,
 Wasm.Binary.Instr.localSet 690,
 Wasm.Binary.Instr.localSet 689] ++ body74Tail1696)

@[cbv_eval] theorem sequence74_tail1688 :
    instructionSequenceAt 3488 false { bytes := artifactBytes, pos := 14479, limit := 15177 } =
      .ok ((body74Tail1688, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 686,
 Wasm.Binary.Instr.localGet 687,
 Wasm.Binary.Instr.localGet 688,
 Wasm.Binary.Instr.call 65,
 Wasm.Binary.Instr.localSet 692,
 Wasm.Binary.Instr.localSet 691,
 Wasm.Binary.Instr.localSet 690,
 Wasm.Binary.Instr.localSet 689] ++ body74Tail1696), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1680 : List Instr := ([Wasm.Binary.Instr.localSet 685,
 Wasm.Binary.Instr.localGet 678,
 Wasm.Binary.Instr.localSet 686,
 Wasm.Binary.Instr.localGet 679,
 Wasm.Binary.Instr.localSet 687,
 Wasm.Binary.Instr.localGet 680,
 Wasm.Binary.Instr.localSet 688,
 Wasm.Binary.Instr.localGet 685] ++ body74Tail1688)

@[cbv_eval] theorem sequence74_tail1680 :
    instructionSequenceAt 3496 false { bytes := artifactBytes, pos := 14455, limit := 15177 } =
      .ok ((body74Tail1680, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 685,
 Wasm.Binary.Instr.localGet 678,
 Wasm.Binary.Instr.localSet 686,
 Wasm.Binary.Instr.localGet 679,
 Wasm.Binary.Instr.localSet 687,
 Wasm.Binary.Instr.localGet 680,
 Wasm.Binary.Instr.localSet 688,
 Wasm.Binary.Instr.localGet 685] ++ body74Tail1688), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1672 : List Instr := ([Wasm.Binary.Instr.localSet 674,
 Wasm.Binary.Instr.localSet 673,
 Wasm.Binary.Instr.localGet 676,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 684,
 Wasm.Binary.Instr.localGet 677] ++ body74Tail1680)

@[cbv_eval] theorem sequence74_tail1672 :
    instructionSequenceAt 3504 false { bytes := artifactBytes, pos := 14437, limit := 15177 } =
      .ok ((body74Tail1672, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 674,
 Wasm.Binary.Instr.localSet 673,
 Wasm.Binary.Instr.localGet 676,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 684,
 Wasm.Binary.Instr.localGet 677] ++ body74Tail1680), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1664 : List Instr := ([Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 787]),
 Wasm.Binary.Instr.localSet 672,
 Wasm.Binary.Instr.localGet 670,
 Wasm.Binary.Instr.localGet 671,
 Wasm.Binary.Instr.localGet 672,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 676,
 Wasm.Binary.Instr.localSet 675] ++ body74Tail1672)

@[cbv_eval] theorem sequence74_tail1664 :
    instructionSequenceAt 3512 false { bytes := artifactBytes, pos := 14409, limit := 15177 } =
      .ok ((body74Tail1664, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 787]),
 Wasm.Binary.Instr.localSet 672,
 Wasm.Binary.Instr.localGet 670,
 Wasm.Binary.Instr.localGet 671,
 Wasm.Binary.Instr.localGet 672,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 676,
 Wasm.Binary.Instr.localSet 675] ++ body74Tail1672), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1656 : List Instr := ([Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 786,
 Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.localGet 786,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 787,
 Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.i64LtU] ++ body74Tail1664)

@[cbv_eval] theorem sequence74_tail1656 :
    instructionSequenceAt 3520 false { bytes := artifactBytes, pos := 14390, limit := 15177 } =
      .ok ((body74Tail1656, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 786,
 Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.localGet 786,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 787,
 Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.i64LtU] ++ body74Tail1664), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1648 : List Instr := ([Wasm.Binary.Instr.localGet 616,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 670,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 671,
 Wasm.Binary.Instr.i64Const 1140,
 Wasm.Binary.Instr.localSet 785] ++ body74Tail1656)

@[cbv_eval] theorem sequence74_tail1648 :
    instructionSequenceAt 3528 false { bytes := artifactBytes, pos := 14370, limit := 15177 } =
      .ok ((body74Tail1648, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 616,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 670,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 671,
 Wasm.Binary.Instr.i64Const 1140,
 Wasm.Binary.Instr.localSet 785] ++ body74Tail1656), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1640 : List Instr := ([Wasm.Binary.Instr.localSet 668,
 Wasm.Binary.Instr.localSet 667,
 Wasm.Binary.Instr.localSet 666,
 Wasm.Binary.Instr.localGet 668,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 683] ++ body74Tail1648)

@[cbv_eval] theorem sequence74_tail1640 :
    instructionSequenceAt 3536 false { bytes := artifactBytes, pos := 14352, limit := 15177 } =
      .ok ((body74Tail1640, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 668,
 Wasm.Binary.Instr.localSet 667,
 Wasm.Binary.Instr.localSet 666,
 Wasm.Binary.Instr.localGet 668,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 683] ++ body74Tail1648), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1632 : List Instr := ([Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 787]),
 Wasm.Binary.Instr.localSet 665,
 Wasm.Binary.Instr.localGet 663,
 Wasm.Binary.Instr.localGet 664,
 Wasm.Binary.Instr.localGet 665,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 669] ++ body74Tail1640)

@[cbv_eval] theorem sequence74_tail1632 :
    instructionSequenceAt 3544 false { bytes := artifactBytes, pos := 14326, limit := 15177 } =
      .ok ((body74Tail1632, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 787]),
 Wasm.Binary.Instr.localSet 665,
 Wasm.Binary.Instr.localGet 663,
 Wasm.Binary.Instr.localGet 664,
 Wasm.Binary.Instr.localGet 665,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 669] ++ body74Tail1640), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1624 : List Instr := ([Wasm.Binary.Instr.localSet 785,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 786,
 Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.localGet 786,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 787,
 Wasm.Binary.Instr.localGet 785] ++ body74Tail1632)

@[cbv_eval] theorem sequence74_tail1624 :
    instructionSequenceAt 3552 false { bytes := artifactBytes, pos := 14305, limit := 15177 } =
      .ok ((body74Tail1624, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 785,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 786,
 Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.localGet 786,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 787,
 Wasm.Binary.Instr.localGet 785] ++ body74Tail1632), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1616 : List Instr := ([Wasm.Binary.Instr.localSet 682,
 Wasm.Binary.Instr.localGet 615,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 663,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 664,
 Wasm.Binary.Instr.i64Const 1140] ++ body74Tail1624)

@[cbv_eval] theorem sequence74_tail1616 :
    instructionSequenceAt 3560 false { bytes := artifactBytes, pos := 14285, limit := 15177 } =
      .ok ((body74Tail1616, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 682,
 Wasm.Binary.Instr.localGet 615,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 663,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 664,
 Wasm.Binary.Instr.i64Const 1140] ++ body74Tail1624), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1608 : List Instr := ([Wasm.Binary.Instr.localSet 662,
 Wasm.Binary.Instr.localSet 661,
 Wasm.Binary.Instr.localSet 660,
 Wasm.Binary.Instr.localSet 659,
 Wasm.Binary.Instr.localGet 660,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64] ++ body74Tail1616)

@[cbv_eval] theorem sequence74_tail1608 :
    instructionSequenceAt 3568 false { bytes := artifactBytes, pos := 14267, limit := 15177 } =
      .ok ((body74Tail1608, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 662,
 Wasm.Binary.Instr.localSet 661,
 Wasm.Binary.Instr.localSet 660,
 Wasm.Binary.Instr.localSet 659,
 Wasm.Binary.Instr.localGet 660,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64] ++ body74Tail1616), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1600 : List Instr := ([Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 787]),
 Wasm.Binary.Instr.localSet 658,
 Wasm.Binary.Instr.localGet 656,
 Wasm.Binary.Instr.localGet 657,
 Wasm.Binary.Instr.localGet 658,
 Wasm.Binary.Instr.call 5] ++ body74Tail1608)

@[cbv_eval] theorem sequence74_tail1600 :
    instructionSequenceAt 3576 false { bytes := artifactBytes, pos := 14241, limit := 15177 } =
      .ok ((body74Tail1600, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 787]),
 Wasm.Binary.Instr.localSet 658,
 Wasm.Binary.Instr.localGet 656,
 Wasm.Binary.Instr.localGet 657,
 Wasm.Binary.Instr.localGet 658,
 Wasm.Binary.Instr.call 5] ++ body74Tail1608), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1592 : List Instr := ([Wasm.Binary.Instr.i64Const 1140,
 Wasm.Binary.Instr.localSet 785,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 786,
 Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.localGet 786,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 787] ++ body74Tail1600)

@[cbv_eval] theorem sequence74_tail1592 :
    instructionSequenceAt 3584 false { bytes := artifactBytes, pos := 14220, limit := 15177 } =
      .ok ((body74Tail1592, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 1140,
 Wasm.Binary.Instr.localSet 785,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 786,
 Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.localGet 786,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 787] ++ body74Tail1600), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1584 : List Instr := ([Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 681,
 Wasm.Binary.Instr.localGet 614,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 656,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 657] ++ body74Tail1592)

@[cbv_eval] theorem sequence74_tail1584 :
    instructionSequenceAt 3592 false { bytes := artifactBytes, pos := 14202, limit := 15177 } =
      .ok ((body74Tail1584, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 681,
 Wasm.Binary.Instr.localGet 614,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 656,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 657] ++ body74Tail1592), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1576 : List Instr := ([Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 655,
 Wasm.Binary.Instr.localSet 654,
 Wasm.Binary.Instr.localSet 653,
 Wasm.Binary.Instr.localSet 652,
 Wasm.Binary.Instr.localGet 652,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add] ++ body74Tail1584)

@[cbv_eval] theorem sequence74_tail1576 :
    instructionSequenceAt 3600 false { bytes := artifactBytes, pos := 14183, limit := 15177 } =
      .ok ((body74Tail1576, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 655,
 Wasm.Binary.Instr.localSet 654,
 Wasm.Binary.Instr.localSet 653,
 Wasm.Binary.Instr.localSet 652,
 Wasm.Binary.Instr.localGet 652,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add] ++ body74Tail1584), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1568 : List Instr := ([Wasm.Binary.Instr.localTee 787,
 Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 787]),
 Wasm.Binary.Instr.localSet 651,
 Wasm.Binary.Instr.localGet 649,
 Wasm.Binary.Instr.localGet 650,
 Wasm.Binary.Instr.localGet 651] ++ body74Tail1576)

@[cbv_eval] theorem sequence74_tail1568 :
    instructionSequenceAt 3608 false { bytes := artifactBytes, pos := 14156, limit := 15177 } =
      .ok ((body74Tail1568, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localTee 787,
 Wasm.Binary.Instr.localGet 785,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 787]),
 Wasm.Binary.Instr.localSet 651,
 Wasm.Binary.Instr.localGet 649,
 Wasm.Binary.Instr.localGet 650,
 Wasm.Binary.Instr.localGet 651] ++ body74Tail1576), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
