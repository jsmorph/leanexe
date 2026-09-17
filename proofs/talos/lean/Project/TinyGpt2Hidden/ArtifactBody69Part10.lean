import Project.TinyGpt2Hidden.ArtifactBody69Part9

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body69Tail224 : List Instr := ([Wasm.Binary.Instr.i64Const 6,
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
       (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])])] ++ body69Tail232)

@[cbv_eval] theorem sequence69_tail224 :
    instructionSequenceAt 742 false { bytes := artifactBytes, pos := 9044, limit := 9325 } =
      .ok ((body69Tail224, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 6,
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
       (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])])] ++ body69Tail232), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail216 : List Instr := ([Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
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
 Wasm.Binary.Instr.localSet 26,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 36] ++ body69Tail224)

@[cbv_eval] theorem sequence69_tail216 :
    instructionSequenceAt 750 false { bytes := artifactBytes, pos := 9007, limit := 9325 } =
      .ok ((body69Tail216, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
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
 Wasm.Binary.Instr.localSet 26,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 36] ++ body69Tail224), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail208 : List Instr := ([Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35]),
 Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.i32WrapI64] ++ body69Tail216)

@[cbv_eval] theorem sequence69_tail208 :
    instructionSequenceAt 758 false { bytes := artifactBytes, pos := 8988, limit := 9325 } =
      .ok ((body69Tail208, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
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
 Wasm.Binary.Instr.i32WrapI64] ++ body69Tail216), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail200 : List Instr := ([Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 38]),
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.i64Add] ++ body69Tail208)

@[cbv_eval] theorem sequence69_tail200 :
    instructionSequenceAt 766 false { bytes := artifactBytes, pos := 8969, limit := 9325 } =
      .ok ((body69Tail200, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
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
 Wasm.Binary.Instr.i64Add] ++ body69Tail208), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail192 : List Instr := ([Wasm.Binary.Instr.i64Eq,
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
       (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])]),
 Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 38,
 Wasm.Binary.Instr.localGet 36] ++ body69Tail200)

@[cbv_eval] theorem sequence69_tail192 :
    instructionSequenceAt 774 false { bytes := artifactBytes, pos := 8933, limit := 9325 } =
      .ok ((body69Tail192, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Eq,
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
       (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])]),
 Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 38,
 Wasm.Binary.Instr.localGet 36] ++ body69Tail200), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail184 : List Instr := ([Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.i64Const 5,
 Wasm.Binary.Instr.localSet 39,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 40,
 Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.i64Const 0] ++ body69Tail192)

@[cbv_eval] theorem sequence69_tail184 :
    instructionSequenceAt 782 false { bytes := artifactBytes, pos := 8917, limit := 9325 } =
      .ok ((body69Tail184, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.i64Const 5,
 Wasm.Binary.Instr.localSet 39,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 40,
 Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.i64Const 0] ++ body69Tail192), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail176 : List Instr := ([Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.i32WrapI64,
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
 Wasm.Binary.Instr.localSet 25,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31] ++ body69Tail184)

@[cbv_eval] theorem sequence69_tail176 :
    instructionSequenceAt 790 false { bytes := artifactBytes, pos := 8881, limit := 9325 } =
      .ok ((body69Tail176, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.i32WrapI64,
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
 Wasm.Binary.Instr.localSet 25,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31] ++ body69Tail184), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail168 : List Instr := ([Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35]),
 Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.localGet 32] ++ body69Tail176)

@[cbv_eval] theorem sequence69_tail168 :
    instructionSequenceAt 798 false { bytes := artifactBytes, pos := 8862, limit := 9325 } =
      .ok ((body69Tail168, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35]),
 Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.localGet 32] ++ body69Tail176), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail160 : List Instr := ([Wasm.Binary.Instr.localTee 38,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 38]),
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33] ++ body69Tail168)

@[cbv_eval] theorem sequence69_tail160 :
    instructionSequenceAt 806 false { bytes := artifactBytes, pos := 8842, limit := 9325 } =
      .ok ((body69Tail160, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localTee 38,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 38]),
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33] ++ body69Tail168), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail152 : List Instr := ([Wasm.Binary.Instr.localGet 40,
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
       (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])]),
 Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.i64Add] ++ body69Tail160)

@[cbv_eval] theorem sequence69_tail152 :
    instructionSequenceAt 814 false { bytes := artifactBytes, pos := 8806, limit := 9325 } =
      .ok ((body69Tail152, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 40,
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
       (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])]),
 Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.i64Add] ++ body69Tail160), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail144 : List Instr := ([Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 39,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 40] ++ body69Tail152)

@[cbv_eval] theorem sequence69_tail144 :
    instructionSequenceAt 822 false { bytes := artifactBytes, pos := 8790, limit := 9325 } =
      .ok ((body69Tail144, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 39,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 40] ++ body69Tail152), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail136 : List Instr := ([Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.i32WrapI64,
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
 Wasm.Binary.Instr.localSet 24] ++ body69Tail144)

@[cbv_eval] theorem sequence69_tail136 :
    instructionSequenceAt 830 false { bytes := artifactBytes, pos := 8754, limit := 9325 } =
      .ok ((body69Tail136, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.i32WrapI64,
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
 Wasm.Binary.Instr.localSet 24] ++ body69Tail144), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail128 : List Instr := ([Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35])] ++ body69Tail136)

@[cbv_eval] theorem sequence69_tail128 :
    instructionSequenceAt 838 false { bytes := artifactBytes, pos := 8735, limit := 9325 } =
      .ok ((body69Tail128, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35])] ++ body69Tail136), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail120 : List Instr := ([Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 38,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 38]),
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4] ++ body69Tail128)

@[cbv_eval] theorem sequence69_tail120 :
    instructionSequenceAt 846 false { bytes := artifactBytes, pos := 8716, limit := 9325 } =
      .ok ((body69Tail120, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 38,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 38]),
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4] ++ body69Tail128), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail112 : List Instr := ([Wasm.Binary.Instr.localGet 3,
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
       (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])]),
 Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 36] ++ body69Tail120)

@[cbv_eval] theorem sequence69_tail112 :
    instructionSequenceAt 854 false { bytes := artifactBytes, pos := 8679, limit := 9325 } =
      .ok ((body69Tail112, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 3,
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
       (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])]),
 Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 36] ++ body69Tail120), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail104 : List Instr := ([Wasm.Binary.Instr.iff
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
 Wasm.Binary.Instr.localSet 23,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.i64Const 3,
 Wasm.Binary.Instr.localSet 39] ++ body69Tail112)

@[cbv_eval] theorem sequence69_tail104 :
    instructionSequenceAt 862 false { bytes := artifactBytes, pos := 8642, limit := 9325 } =
      .ok ((body69Tail104, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.iff
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
 Wasm.Binary.Instr.localSet 23,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.i64Const 3,
 Wasm.Binary.Instr.localSet 39] ++ body69Tail112), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
