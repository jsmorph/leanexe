import Project.TinyGpt2Hidden.ArtifactBody69Part8

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence69_294_t_tail8 :
    instructionSequenceAt 662 true { bytes := artifactBytes, pos := 9272, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Add, Wasm.Binary.Instr.i32WrapI64, Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 9278, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_294_t_tail0 :
    instructionSequenceAt 670 true { bytes := artifactBytes, pos := 9259, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Mul,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Mul,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 9278, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_294_e_tail1 :
    instructionSequenceAt 669 false { bytes := artifactBytes, pos := 9279, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 9280, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_294_e_tail0 :
    instructionSequenceAt 670 false { bytes := artifactBytes, pos := 9278, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 9280, limit := 9325 }) := by
  cbv

@[cbv_opaque] def body69Tail317 : List Instr := []

@[cbv_eval] theorem sequence69_tail317 :
    instructionSequenceAt 649 false { bytes := artifactBytes, pos := 9324, limit := 9325 } =
      .ok ((body69Tail317, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok (([], .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail312 : List Instr := ([Wasm.Binary.Instr.call 68,
 Wasm.Binary.Instr.localSet 29,
 Wasm.Binary.Instr.localGet 29,
 Wasm.Binary.Instr.localSet 30,
 Wasm.Binary.Instr.localGet 30] ++ body69Tail317)

@[cbv_eval] theorem sequence69_tail312 :
    instructionSequenceAt 654 false { bytes := artifactBytes, pos := 9314, limit := 9325 } =
      .ok ((body69Tail312, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 68,
 Wasm.Binary.Instr.localSet 29,
 Wasm.Binary.Instr.localGet 29,
 Wasm.Binary.Instr.localSet 30,
 Wasm.Binary.Instr.localGet 30] ++ body69Tail317), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail304 : List Instr := ([Wasm.Binary.Instr.localGet 21,
 Wasm.Binary.Instr.localGet 22,
 Wasm.Binary.Instr.localGet 23,
 Wasm.Binary.Instr.localGet 24,
 Wasm.Binary.Instr.localGet 25,
 Wasm.Binary.Instr.localGet 26,
 Wasm.Binary.Instr.localGet 27,
 Wasm.Binary.Instr.localGet 28] ++ body69Tail312)

@[cbv_eval] theorem sequence69_tail304 :
    instructionSequenceAt 662 false { bytes := artifactBytes, pos := 9298, limit := 9325 } =
      .ok ((body69Tail304, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 21,
 Wasm.Binary.Instr.localGet 22,
 Wasm.Binary.Instr.localGet 23,
 Wasm.Binary.Instr.localGet 24,
 Wasm.Binary.Instr.localGet 25,
 Wasm.Binary.Instr.localGet 26,
 Wasm.Binary.Instr.localGet 27,
 Wasm.Binary.Instr.localGet 28] ++ body69Tail312), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail296 : List Instr := ([Wasm.Binary.Instr.localGet 13,
 Wasm.Binary.Instr.localGet 14,
 Wasm.Binary.Instr.localGet 15,
 Wasm.Binary.Instr.localGet 16,
 Wasm.Binary.Instr.localGet 17,
 Wasm.Binary.Instr.localGet 18,
 Wasm.Binary.Instr.localGet 19,
 Wasm.Binary.Instr.localGet 20] ++ body69Tail304)

@[cbv_eval] theorem sequence69_tail296 :
    instructionSequenceAt 670 false { bytes := artifactBytes, pos := 9282, limit := 9325 } =
      .ok ((body69Tail296, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 13,
 Wasm.Binary.Instr.localGet 14,
 Wasm.Binary.Instr.localGet 15,
 Wasm.Binary.Instr.localGet 16,
 Wasm.Binary.Instr.localGet 17,
 Wasm.Binary.Instr.localGet 18,
 Wasm.Binary.Instr.localGet 19,
 Wasm.Binary.Instr.localGet 20] ++ body69Tail304), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail288 : List Instr := ([Wasm.Binary.Instr.localSet 32,
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
 Wasm.Binary.Instr.localSet 28] ++ body69Tail296)

@[cbv_eval] theorem sequence69_tail288 :
    instructionSequenceAt 678 false { bytes := artifactBytes, pos := 9246, limit := 9325 } =
      .ok ((body69Tail288, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
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
 Wasm.Binary.Instr.localSet 28] ++ body69Tail296), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail280 : List Instr := ([Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35])] ++ body69Tail288)

@[cbv_eval] theorem sequence69_tail280 :
    instructionSequenceAt 686 false { bytes := artifactBytes, pos := 9227, limit := 9325 } =
      .ok ((body69Tail280, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
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
   (some [Wasm.Binary.Instr.localGet 35])] ++ body69Tail288), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail272 : List Instr := ([Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 38,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 38]),
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4] ++ body69Tail280)

@[cbv_eval] theorem sequence69_tail272 :
    instructionSequenceAt 694 false { bytes := artifactBytes, pos := 9208, limit := 9325 } =
      .ok ((body69Tail272, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
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
 Wasm.Binary.Instr.localGet 4] ++ body69Tail280), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail264 : List Instr := ([Wasm.Binary.Instr.localGet 3,
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
 Wasm.Binary.Instr.localGet 36] ++ body69Tail272)

@[cbv_eval] theorem sequence69_tail264 :
    instructionSequenceAt 702 false { bytes := artifactBytes, pos := 9171, limit := 9325 } =
      .ok ((body69Tail264, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
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
 Wasm.Binary.Instr.localGet 36] ++ body69Tail272), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail256 : List Instr := ([Wasm.Binary.Instr.iff
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
 Wasm.Binary.Instr.localSet 27,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.i64Const 7,
 Wasm.Binary.Instr.localSet 39] ++ body69Tail264)

@[cbv_eval] theorem sequence69_tail256 :
    instructionSequenceAt 710 false { bytes := artifactBytes, pos := 9134, limit := 9325 } =
      .ok ((body69Tail256, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
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
 Wasm.Binary.Instr.localSet 27,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.i64Const 7,
 Wasm.Binary.Instr.localSet 39] ++ body69Tail264), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail248 : List Instr := ([Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 35]),
 Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.i64LtU] ++ body69Tail256)

@[cbv_eval] theorem sequence69_tail248 :
    instructionSequenceAt 718 false { bytes := artifactBytes, pos := 9115, limit := 9325 } =
      .ok ((body69Tail248, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
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
 Wasm.Binary.Instr.i64LtU] ++ body69Tail256), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail240 : List Instr := ([Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33] ++ body69Tail248)

@[cbv_eval] theorem sequence69_tail240 :
    instructionSequenceAt 726 false { bytes := artifactBytes, pos := 9100, limit := 9325 } =
      .ok ((body69Tail240, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 35,
 Wasm.Binary.Instr.localGet 33] ++ body69Tail248), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body69Tail232 : List Instr := ([Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localTee 38,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 38])] ++ body69Tail240)

@[cbv_eval] theorem sequence69_tail232 :
    instructionSequenceAt 734 false { bytes := artifactBytes, pos := 9081, limit := 9325 } =
      .ok ((body69Tail232, .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) := by
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
   (some [Wasm.Binary.Instr.localGet 38])] ++ body69Tail240), .end), { bytes := artifactBytes, pos := 9325, limit := 9325 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
