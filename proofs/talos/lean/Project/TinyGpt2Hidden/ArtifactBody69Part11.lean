import Project.TinyGpt2Hidden.ArtifactBody69Part10

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body69Tail96 : List Instr := ([Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35]),
 Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.i64LtU] ++ body69Tail104)

@[cbv_eval] theorem sequence69_tail96 :
    instructionSequenceAt 870 false { bytes := artifactBytes, pos := 8623, limit := 9325 } =
      .ok ((body69Tail96, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35]),
 Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.i64LtU] ++ body69Tail104), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail88 : List Instr := ([Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33] ++ body69Tail96)

@[cbv_eval] theorem sequence69_tail88 :
    instructionSequenceAt 878 false { bytes := artifactBytes, pos := 8608, limit := 9325 } =
      .ok ((body69Tail88, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33] ++ body69Tail96), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail80 : List Instr := ([Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 38,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 38])] ++ body69Tail88)

@[cbv_eval] theorem sequence69_tail80 :
    instructionSequenceAt 886 false { bytes := artifactBytes, pos := 8589, limit := 9325 } =
      .ok ((body69Tail80, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 38,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 38])] ++ body69Tail88), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail72 : List Instr := ([Wasm.Binary.Instr.i64Const 2,
 Wasm.Binary.Instr.localSet 39,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 40,
 Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.i64Const 0]
   (some [Wasm.Binary.Instr.i64Const (-1),
     Wasm.Binary.Instr.localGet 40,
     Wasm.Binary.Instr.i64DivU,
     Wasm.Binary.Instr.localGet 39,
     Wasm.Binary.Instr.i64LtU,
     Wasm.Binary.Instr.iff
       (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
       [Wasm.Binary.Instr.unreachable]
       (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])])] ++ body69Tail80)

@[cbv_eval] theorem sequence69_tail72 :
    instructionSequenceAt 894 false { bytes := artifactBytes, pos := 8552, limit := 9325 } =
      .ok ((body69Tail72, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 2,
 Wasm.Binary.Instr.localSet 39,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 40,
 Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.i64Const 0]
   (some [Wasm.Binary.Instr.i64Const (-1),
     Wasm.Binary.Instr.localGet 40,
     Wasm.Binary.Instr.i64DivU,
     Wasm.Binary.Instr.localGet 39,
     Wasm.Binary.Instr.i64LtU,
     Wasm.Binary.Instr.iff
       (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
       [Wasm.Binary.Instr.unreachable]
       (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])])] ++ body69Tail80), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail64 : List Instr := ([Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.localGet 31,
    Wasm.Binary.Instr.localGet 32,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }]
   (some [Wasm.Binary.Instr.unreachable]),
 Wasm.Binary.Instr.localSet 22,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 36] ++ body69Tail72)

@[cbv_eval] theorem sequence69_tail64 :
    instructionSequenceAt 902 false { bytes := artifactBytes, pos := 8515, limit := 9325 } =
      .ok ((body69Tail64, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.localGet 31,
    Wasm.Binary.Instr.localGet 32,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }]
   (some [Wasm.Binary.Instr.unreachable]),
 Wasm.Binary.Instr.localSet 22,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 36] ++ body69Tail72), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail56 : List Instr := ([Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35]),
 Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.i32WrapI64] ++ body69Tail64)

@[cbv_eval] theorem sequence69_tail56 :
    instructionSequenceAt 910 false { bytes := artifactBytes, pos := 8496, limit := 9325 } =
      .ok ((body69Tail56, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35]),
 Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.i32WrapI64] ++ body69Tail64), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail48 : List Instr := ([Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 38]),
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.i64Add] ++ body69Tail56)

@[cbv_eval] theorem sequence69_tail48 :
    instructionSequenceAt 918 false { bytes := artifactBytes, pos := 8477, limit := 9325 } =
      .ok ((body69Tail48, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 38]),
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.i64Add] ++ body69Tail56), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail40 : List Instr := ([Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 38,
 Wasm.Binary.Instr.localGet 36] ++ body69Tail48)

@[cbv_eval] theorem sequence69_tail40 :
    instructionSequenceAt 926 false { bytes := artifactBytes, pos := 8462, limit := 9325 } =
      .ok ((body69Tail40, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 38,
 Wasm.Binary.Instr.localGet 36] ++ body69Tail48), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail32 : List Instr := ([Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.localGet 31,
    Wasm.Binary.Instr.localGet 32,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }]
   (some [Wasm.Binary.Instr.unreachable]),
 Wasm.Binary.Instr.localSet 21,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2] ++ body69Tail40)

@[cbv_eval] theorem sequence69_tail32 :
    instructionSequenceAt 934 false { bytes := artifactBytes, pos := 8426, limit := 9325 } =
      .ok ((body69Tail32, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.localGet 31,
    Wasm.Binary.Instr.localGet 32,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }]
   (some [Wasm.Binary.Instr.unreachable]),
 Wasm.Binary.Instr.localSet 21,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2] ++ body69Tail40), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail24 : List Instr := ([Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35]),
 Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 31] ++ body69Tail32)

@[cbv_eval] theorem sequence69_tail24 :
    instructionSequenceAt 942 false { bytes := artifactBytes, pos := 8407, limit := 9325 } =
      .ok ((body69Tail24, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35]),
 Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 31] ++ body69Tail32), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail16 : List Instr := ([Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34] ++ body69Tail24)

@[cbv_eval] theorem sequence69_tail16 :
    instructionSequenceAt 950 false { bytes := artifactBytes, pos := 8391, limit := 9325 } =
      .ok ((body69Tail16, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34] ++ body69Tail24), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail8 : List Instr := ([Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.localSet 17,
 Wasm.Binary.Instr.localGet 10,
 Wasm.Binary.Instr.localSet 18,
 Wasm.Binary.Instr.localGet 11,
 Wasm.Binary.Instr.localSet 19,
 Wasm.Binary.Instr.localGet 12,
 Wasm.Binary.Instr.localSet 20] ++ body69Tail16)

@[cbv_eval] theorem sequence69_tail8 :
    instructionSequenceAt 958 false { bytes := artifactBytes, pos := 8375, limit := 9325 } =
      .ok ((body69Tail8, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.localSet 17,
 Wasm.Binary.Instr.localGet 10,
 Wasm.Binary.Instr.localSet 18,
 Wasm.Binary.Instr.localGet 11,
 Wasm.Binary.Instr.localSet 19,
 Wasm.Binary.Instr.localGet 12,
 Wasm.Binary.Instr.localSet 20] ++ body69Tail16), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail0 : List Instr := ([Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 13,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localSet 14,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localSet 15,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localSet 16] ++ body69Tail8)

@[cbv_eval] theorem sequence69_tail0 :
    instructionSequenceAt 966 false { bytes := artifactBytes, pos := 8359, limit := 9325 } =
      .ok ((body69Tail0, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 13,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localSet 14,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localSet 15,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localSet 16] ++ body69Tail8), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
