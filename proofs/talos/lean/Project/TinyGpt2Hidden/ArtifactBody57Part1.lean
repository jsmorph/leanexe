import Project.TinyGpt2Hidden.ArtifactBody57Part0

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body57Tail488 : List Instr := []

@[cbv_eval] theorem sequence57_tail488 :
    instructionSequenceAt 570 false { bytes := artifactBytes, pos := 7738, limit := 7739 } =
      .ok ((body57Tail488, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok (([], .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail480 : List Instr := ([Wasm.Binary.Instr.localGet 162,
 Wasm.Binary.Instr.localGet 163,
 Wasm.Binary.Instr.localGet 164,
 Wasm.Binary.Instr.localGet 165,
 Wasm.Binary.Instr.localGet 166,
 Wasm.Binary.Instr.localGet 167,
 Wasm.Binary.Instr.localGet 168,
 Wasm.Binary.Instr.localGet 169] ++ body57Tail488)

@[cbv_eval] theorem sequence57_tail480 :
    instructionSequenceAt 578 false { bytes := artifactBytes, pos := 7714, limit := 7739 } =
      .ok ((body57Tail480, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 162,
 Wasm.Binary.Instr.localGet 163,
 Wasm.Binary.Instr.localGet 164,
 Wasm.Binary.Instr.localGet 165,
 Wasm.Binary.Instr.localGet 166,
 Wasm.Binary.Instr.localGet 167,
 Wasm.Binary.Instr.localGet 168,
 Wasm.Binary.Instr.localGet 169] ++ body57Tail488), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail472 : List Instr := ([Wasm.Binary.Instr.localSet 160,
 Wasm.Binary.Instr.localSet 159,
 Wasm.Binary.Instr.localSet 158,
 Wasm.Binary.Instr.localGet 161,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 169] ++ body57Tail480)

@[cbv_eval] theorem sequence57_tail472 :
    instructionSequenceAt 586 false { bytes := artifactBytes, pos := 7696, limit := 7739 } =
      .ok ((body57Tail472, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 160,
 Wasm.Binary.Instr.localSet 159,
 Wasm.Binary.Instr.localSet 158,
 Wasm.Binary.Instr.localGet 161,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 169] ++ body57Tail480), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail464 : List Instr := ([Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 172]),
 Wasm.Binary.Instr.localSet 157,
 Wasm.Binary.Instr.localGet 155,
 Wasm.Binary.Instr.localGet 156,
 Wasm.Binary.Instr.localGet 157,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 161] ++ body57Tail472)

@[cbv_eval] theorem sequence57_tail464 :
    instructionSequenceAt 594 false { bytes := artifactBytes, pos := 7670, limit := 7739 } =
      .ok ((body57Tail464, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 172]),
 Wasm.Binary.Instr.localSet 157,
 Wasm.Binary.Instr.localGet 155,
 Wasm.Binary.Instr.localGet 156,
 Wasm.Binary.Instr.localGet 157,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 161] ++ body57Tail472), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail456 : List Instr := ([Wasm.Binary.Instr.localSet 170,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 171,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.localGet 171,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 172,
 Wasm.Binary.Instr.localGet 170] ++ body57Tail464)

@[cbv_eval] theorem sequence57_tail456 :
    instructionSequenceAt 602 false { bytes := artifactBytes, pos := 7649, limit := 7739 } =
      .ok ((body57Tail456, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 170,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 171,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.localGet 171,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 172,
 Wasm.Binary.Instr.localGet 170] ++ body57Tail464), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail448 : List Instr := ([Wasm.Binary.Instr.localSet 168,
 Wasm.Binary.Instr.localGet 101,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 155,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 156,
 Wasm.Binary.Instr.i64Const 1140] ++ body57Tail456)

@[cbv_eval] theorem sequence57_tail448 :
    instructionSequenceAt 610 false { bytes := artifactBytes, pos := 7630, limit := 7739 } =
      .ok ((body57Tail448, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 168,
 Wasm.Binary.Instr.localGet 101,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 155,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 156,
 Wasm.Binary.Instr.i64Const 1140] ++ body57Tail456), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail440 : List Instr := ([Wasm.Binary.Instr.localSet 154,
 Wasm.Binary.Instr.localSet 153,
 Wasm.Binary.Instr.localSet 152,
 Wasm.Binary.Instr.localSet 151,
 Wasm.Binary.Instr.localGet 153,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64] ++ body57Tail448)

@[cbv_eval] theorem sequence57_tail440 :
    instructionSequenceAt 618 false { bytes := artifactBytes, pos := 7612, limit := 7739 } =
      .ok ((body57Tail440, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 154,
 Wasm.Binary.Instr.localSet 153,
 Wasm.Binary.Instr.localSet 152,
 Wasm.Binary.Instr.localSet 151,
 Wasm.Binary.Instr.localGet 153,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64] ++ body57Tail448), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail432 : List Instr := ([Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 172]),
 Wasm.Binary.Instr.localSet 150,
 Wasm.Binary.Instr.localGet 148,
 Wasm.Binary.Instr.localGet 149,
 Wasm.Binary.Instr.localGet 150,
 Wasm.Binary.Instr.call 5] ++ body57Tail440)

@[cbv_eval] theorem sequence57_tail432 :
    instructionSequenceAt 626 false { bytes := artifactBytes, pos := 7586, limit := 7739 } =
      .ok ((body57Tail432, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 172]),
 Wasm.Binary.Instr.localSet 150,
 Wasm.Binary.Instr.localGet 148,
 Wasm.Binary.Instr.localGet 149,
 Wasm.Binary.Instr.localGet 150,
 Wasm.Binary.Instr.call 5] ++ body57Tail440), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail424 : List Instr := ([Wasm.Binary.Instr.i64Const 1140,
 Wasm.Binary.Instr.localSet 170,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 171,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.localGet 171,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 172] ++ body57Tail432)

@[cbv_eval] theorem sequence57_tail424 :
    instructionSequenceAt 634 false { bytes := artifactBytes, pos := 7565, limit := 7739 } =
      .ok ((body57Tail424, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 1140,
 Wasm.Binary.Instr.localSet 170,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 171,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.localGet 171,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 172] ++ body57Tail432), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail416 : List Instr := ([Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 167,
 Wasm.Binary.Instr.localGet 100,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 148,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 149] ++ body57Tail424)

@[cbv_eval] theorem sequence57_tail416 :
    instructionSequenceAt 642 false { bytes := artifactBytes, pos := 7548, limit := 7739 } =
      .ok ((body57Tail416, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 167,
 Wasm.Binary.Instr.localGet 100,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 148,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 149] ++ body57Tail424), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail408 : List Instr := ([Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 147,
 Wasm.Binary.Instr.localSet 146,
 Wasm.Binary.Instr.localSet 145,
 Wasm.Binary.Instr.localSet 144,
 Wasm.Binary.Instr.localGet 145,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add] ++ body57Tail416)

@[cbv_eval] theorem sequence57_tail408 :
    instructionSequenceAt 650 false { bytes := artifactBytes, pos := 7529, limit := 7739 } =
      .ok ((body57Tail408, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 147,
 Wasm.Binary.Instr.localSet 146,
 Wasm.Binary.Instr.localSet 145,
 Wasm.Binary.Instr.localSet 144,
 Wasm.Binary.Instr.localGet 145,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add] ++ body57Tail416), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail400 : List Instr := ([Wasm.Binary.Instr.localTee 172,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 172]),
 Wasm.Binary.Instr.localSet 143,
 Wasm.Binary.Instr.localGet 141,
 Wasm.Binary.Instr.localGet 142,
 Wasm.Binary.Instr.localGet 143] ++ body57Tail408)

@[cbv_eval] theorem sequence57_tail400 :
    instructionSequenceAt 658 false { bytes := artifactBytes, pos := 7502, limit := 7739 } =
      .ok ((body57Tail400, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localTee 172,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 172]),
 Wasm.Binary.Instr.localSet 143,
 Wasm.Binary.Instr.localGet 141,
 Wasm.Binary.Instr.localGet 142,
 Wasm.Binary.Instr.localGet 143] ++ body57Tail408), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail392 : List Instr := ([Wasm.Binary.Instr.localSet 142,
 Wasm.Binary.Instr.i64Const 1140,
 Wasm.Binary.Instr.localSet 170,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 171,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.localGet 171,
 Wasm.Binary.Instr.i64Add] ++ body57Tail400)

@[cbv_eval] theorem sequence57_tail392 :
    instructionSequenceAt 666 false { bytes := artifactBytes, pos := 7481, limit := 7739 } =
      .ok ((body57Tail392, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 142,
 Wasm.Binary.Instr.i64Const 1140,
 Wasm.Binary.Instr.localSet 170,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 171,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.localGet 171,
 Wasm.Binary.Instr.i64Add] ++ body57Tail400), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail384 : List Instr := ([Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 166,
 Wasm.Binary.Instr.localGet 99,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 141,
 Wasm.Binary.Instr.localGet 1] ++ body57Tail392)

@[cbv_eval] theorem sequence57_tail384 :
    instructionSequenceAt 674 false { bytes := artifactBytes, pos := 7466, limit := 7739 } =
      .ok ((body57Tail384, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 166,
 Wasm.Binary.Instr.localGet 99,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 141,
 Wasm.Binary.Instr.localGet 1] ++ body57Tail392), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail376 : List Instr := ([Wasm.Binary.Instr.localGet 136,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 140,
 Wasm.Binary.Instr.localSet 139,
 Wasm.Binary.Instr.localSet 138,
 Wasm.Binary.Instr.localSet 137,
 Wasm.Binary.Instr.localGet 137,
 Wasm.Binary.Instr.f64ReinterpretI64] ++ body57Tail384)

@[cbv_eval] theorem sequence57_tail376 :
    instructionSequenceAt 682 false { bytes := artifactBytes, pos := 7445, limit := 7739 } =
      .ok ((body57Tail376, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 136,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 140,
 Wasm.Binary.Instr.localSet 139,
 Wasm.Binary.Instr.localSet 138,
 Wasm.Binary.Instr.localSet 137,
 Wasm.Binary.Instr.localGet 137,
 Wasm.Binary.Instr.f64ReinterpretI64] ++ body57Tail384), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail368 : List Instr := ([Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 172,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 172]),
 Wasm.Binary.Instr.localSet 136,
 Wasm.Binary.Instr.localGet 134,
 Wasm.Binary.Instr.localGet 135] ++ body57Tail376)

@[cbv_eval] theorem sequence57_tail368 :
    instructionSequenceAt 690 false { bytes := artifactBytes, pos := 7420, limit := 7739 } =
      .ok ((body57Tail368, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 172,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 172]),
 Wasm.Binary.Instr.localSet 136,
 Wasm.Binary.Instr.localGet 134,
 Wasm.Binary.Instr.localGet 135] ++ body57Tail376), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
