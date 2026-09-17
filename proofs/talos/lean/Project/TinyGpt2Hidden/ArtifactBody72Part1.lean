import Project.TinyGpt2Hidden.ArtifactBody72Part0

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body72Tail144 : List Instr := ([Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 182,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 183,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 184,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 185] ++ body72Tail152)

@[cbv_eval] theorem sequence72_tail144 :
    instructionSequenceAt 484 false { bytes := artifactBytes, pos := 9657, limit := 9983 } =
      .ok ((body72Tail144, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 182,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 183,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 184,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 185] ++ body72Tail152), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail136 : List Instr := ([Wasm.Binary.Instr.call 70,
 Wasm.Binary.Instr.localSet 178,
 Wasm.Binary.Instr.localGet 178,
 Wasm.Binary.Instr.localSet 179,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 180,
 Wasm.Binary.Instr.i64Const 2,
 Wasm.Binary.Instr.localSet 181] ++ body72Tail144)

@[cbv_eval] theorem sequence72_tail136 :
    instructionSequenceAt 492 false { bytes := artifactBytes, pos := 9636, limit := 9983 } =
      .ok ((body72Tail136, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 70,
 Wasm.Binary.Instr.localSet 178,
 Wasm.Binary.Instr.localGet 178,
 Wasm.Binary.Instr.localSet 179,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 180,
 Wasm.Binary.Instr.i64Const 2,
 Wasm.Binary.Instr.localSet 181] ++ body72Tail144), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail128 : List Instr := ([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 283,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 176,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 177] ++ body72Tail136)

@[cbv_eval] theorem sequence72_tail128 :
    instructionSequenceAt 500 false { bytes := artifactBytes, pos := 9620, limit := 9983 } =
      .ok ((body72Tail128, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 283,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 176,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 177] ++ body72Tail136), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail120 : List Instr := ([Wasm.Binary.Instr.localGet 139,
 Wasm.Binary.Instr.localGet 141,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 145,
 Wasm.Binary.Instr.localSet 144,
 Wasm.Binary.Instr.localSet 143,
 Wasm.Binary.Instr.localSet 142,
 Wasm.Binary.Instr.localGet 143] ++ body72Tail128)

@[cbv_eval] theorem sequence72_tail120 :
    instructionSequenceAt 508 false { bytes := artifactBytes, pos := 9597, limit := 9983 } =
      .ok ((body72Tail120, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 139,
 Wasm.Binary.Instr.localGet 141,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 145,
 Wasm.Binary.Instr.localSet 144,
 Wasm.Binary.Instr.localSet 143,
 Wasm.Binary.Instr.localSet 142,
 Wasm.Binary.Instr.localGet 143] ++ body72Tail128), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail112 : List Instr := ([Wasm.Binary.Instr.localSet 138,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 139,
 Wasm.Binary.Instr.call 71,
 Wasm.Binary.Instr.localSet 140,
 Wasm.Binary.Instr.localGet 140,
 Wasm.Binary.Instr.localSet 141,
 Wasm.Binary.Instr.localGet 138] ++ body72Tail120)

@[cbv_eval] theorem sequence72_tail112 :
    instructionSequenceAt 516 false { bytes := artifactBytes, pos := 9575, limit := 9983 } =
      .ok ((body72Tail112, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 138,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 139,
 Wasm.Binary.Instr.call 71,
 Wasm.Binary.Instr.localSet 140,
 Wasm.Binary.Instr.localGet 140,
 Wasm.Binary.Instr.localSet 141,
 Wasm.Binary.Instr.localGet 138] ++ body72Tail120), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail104 : List Instr := ([Wasm.Binary.Instr.localGet 104,
 Wasm.Binary.Instr.localGet 105,
 Wasm.Binary.Instr.localGet 106,
 Wasm.Binary.Instr.call 69,
 Wasm.Binary.Instr.localSet 107,
 Wasm.Binary.Instr.localGet 107,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0] ++ body72Tail112)

@[cbv_eval] theorem sequence72_tail104 :
    instructionSequenceAt 524 false { bytes := artifactBytes, pos := 9560, limit := 9983 } =
      .ok ((body72Tail104, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 104,
 Wasm.Binary.Instr.localGet 105,
 Wasm.Binary.Instr.localGet 106,
 Wasm.Binary.Instr.call 69,
 Wasm.Binary.Instr.localSet 107,
 Wasm.Binary.Instr.localGet 107,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0] ++ body72Tail112), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail96 : List Instr := ([Wasm.Binary.Instr.localGet 96,
 Wasm.Binary.Instr.localGet 97,
 Wasm.Binary.Instr.localGet 98,
 Wasm.Binary.Instr.localGet 99,
 Wasm.Binary.Instr.localGet 100,
 Wasm.Binary.Instr.localGet 101,
 Wasm.Binary.Instr.localGet 102,
 Wasm.Binary.Instr.localGet 103] ++ body72Tail104)

@[cbv_eval] theorem sequence72_tail96 :
    instructionSequenceAt 532 false { bytes := artifactBytes, pos := 9544, limit := 9983 } =
      .ok ((body72Tail96, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 96,
 Wasm.Binary.Instr.localGet 97,
 Wasm.Binary.Instr.localGet 98,
 Wasm.Binary.Instr.localGet 99,
 Wasm.Binary.Instr.localGet 100,
 Wasm.Binary.Instr.localGet 101,
 Wasm.Binary.Instr.localGet 102,
 Wasm.Binary.Instr.localGet 103] ++ body72Tail104), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail88 : List Instr := ([Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localSet 104,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localSet 105,
 Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.localSet 106,
 Wasm.Binary.Instr.localGet 93,
 Wasm.Binary.Instr.localGet 94] ++ body72Tail96)

@[cbv_eval] theorem sequence72_tail88 :
    instructionSequenceAt 540 false { bytes := artifactBytes, pos := 9528, limit := 9983 } =
      .ok ((body72Tail88, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localSet 104,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localSet 105,
 Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.localSet 106,
 Wasm.Binary.Instr.localGet 93,
 Wasm.Binary.Instr.localGet 94] ++ body72Tail96), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail80 : List Instr := ([Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 100,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 101,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 102,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localSet 103] ++ body72Tail88)

@[cbv_eval] theorem sequence72_tail80 :
    instructionSequenceAt 548 false { bytes := artifactBytes, pos := 9512, limit := 9983 } =
      .ok ((body72Tail80, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 100,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 101,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 102,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localSet 103] ++ body72Tail88), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail72 : List Instr := ([Wasm.Binary.Instr.localGet 95,
 Wasm.Binary.Instr.localSet 96,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 97,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.localSet 98,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 99] ++ body72Tail80)

@[cbv_eval] theorem sequence72_tail72 :
    instructionSequenceAt 556 false { bytes := artifactBytes, pos := 9496, limit := 9983 } =
      .ok ((body72Tail72, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 95,
 Wasm.Binary.Instr.localSet 96,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 97,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.localSet 98,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 99] ++ body72Tail80), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail64 : List Instr := ([Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 282,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 93,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 94,
 Wasm.Binary.Instr.call 70,
 Wasm.Binary.Instr.localSet 95] ++ body72Tail72)

@[cbv_eval] theorem sequence72_tail64 :
    instructionSequenceAt 564 false { bytes := artifactBytes, pos := 9480, limit := 9983 } =
      .ok ((body72Tail64, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 282,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 93,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 94,
 Wasm.Binary.Instr.call 70,
 Wasm.Binary.Instr.localSet 95] ++ body72Tail72), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail56 : List Instr := ([Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 77,
 Wasm.Binary.Instr.localSet 76,
 Wasm.Binary.Instr.localSet 75,
 Wasm.Binary.Instr.localSet 74,
 Wasm.Binary.Instr.localGet 74,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add] ++ body72Tail64)

@[cbv_eval] theorem sequence72_tail56 :
    instructionSequenceAt 572 false { bytes := artifactBytes, pos := 9466, limit := 9983 } =
      .ok ((body72Tail56, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 77,
 Wasm.Binary.Instr.localSet 76,
 Wasm.Binary.Instr.localSet 75,
 Wasm.Binary.Instr.localSet 74,
 Wasm.Binary.Instr.localGet 74,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add] ++ body72Tail64), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail48 : List Instr := ([Wasm.Binary.Instr.localSet 71,
 Wasm.Binary.Instr.call 71,
 Wasm.Binary.Instr.localSet 72,
 Wasm.Binary.Instr.localGet 72,
 Wasm.Binary.Instr.localSet 73,
 Wasm.Binary.Instr.localGet 70,
 Wasm.Binary.Instr.localGet 71,
 Wasm.Binary.Instr.localGet 73] ++ body72Tail56)

@[cbv_eval] theorem sequence72_tail48 :
    instructionSequenceAt 580 false { bytes := artifactBytes, pos := 9450, limit := 9983 } =
      .ok ((body72Tail48, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 71,
 Wasm.Binary.Instr.call 71,
 Wasm.Binary.Instr.localSet 72,
 Wasm.Binary.Instr.localGet 72,
 Wasm.Binary.Instr.localSet 73,
 Wasm.Binary.Instr.localGet 70,
 Wasm.Binary.Instr.localGet 71,
 Wasm.Binary.Instr.localGet 73] ++ body72Tail56), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail40 : List Instr := ([Wasm.Binary.Instr.localGet 23,
 Wasm.Binary.Instr.call 69,
 Wasm.Binary.Instr.localSet 24,
 Wasm.Binary.Instr.localGet 24,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 70,
 Wasm.Binary.Instr.localGet 1] ++ body72Tail48)

@[cbv_eval] theorem sequence72_tail40 :
    instructionSequenceAt 588 false { bytes := artifactBytes, pos := 9435, limit := 9983 } =
      .ok ((body72Tail40, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 23,
 Wasm.Binary.Instr.call 69,
 Wasm.Binary.Instr.localSet 24,
 Wasm.Binary.Instr.localGet 24,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 70,
 Wasm.Binary.Instr.localGet 1] ++ body72Tail48), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail32 : List Instr := ([Wasm.Binary.Instr.localGet 15,
 Wasm.Binary.Instr.localGet 16,
 Wasm.Binary.Instr.localGet 17,
 Wasm.Binary.Instr.localGet 18,
 Wasm.Binary.Instr.localGet 19,
 Wasm.Binary.Instr.localGet 20,
 Wasm.Binary.Instr.localGet 21,
 Wasm.Binary.Instr.localGet 22] ++ body72Tail40)

@[cbv_eval] theorem sequence72_tail32 :
    instructionSequenceAt 596 false { bytes := artifactBytes, pos := 9419, limit := 9983 } =
      .ok ((body72Tail32, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 15,
 Wasm.Binary.Instr.localGet 16,
 Wasm.Binary.Instr.localGet 17,
 Wasm.Binary.Instr.localGet 18,
 Wasm.Binary.Instr.localGet 19,
 Wasm.Binary.Instr.localGet 20,
 Wasm.Binary.Instr.localGet 21,
 Wasm.Binary.Instr.localGet 22] ++ body72Tail40), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail24 : List Instr := ([Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localSet 22,
 Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.localSet 23,
 Wasm.Binary.Instr.localGet 10,
 Wasm.Binary.Instr.localGet 11,
 Wasm.Binary.Instr.localGet 13,
 Wasm.Binary.Instr.localGet 14] ++ body72Tail32)

@[cbv_eval] theorem sequence72_tail24 :
    instructionSequenceAt 604 false { bytes := artifactBytes, pos := 9403, limit := 9983 } =
      .ok ((body72Tail24, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localSet 22,
 Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.localSet 23,
 Wasm.Binary.Instr.localGet 10,
 Wasm.Binary.Instr.localGet 11,
 Wasm.Binary.Instr.localGet 13,
 Wasm.Binary.Instr.localGet 14] ++ body72Tail32), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
