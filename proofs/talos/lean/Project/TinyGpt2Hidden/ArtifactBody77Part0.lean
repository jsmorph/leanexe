import Project.Artifact.Binary.InstructionEvaluate
import Project.Artifact.Binary.Equality
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence77_3_t_7_t_tail1 :
    instructionSequenceAt 62 true { bytes := artifactBytes, pos := 15607, limit := 15653 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15608, limit := 15653 }) := by
  cbv

@[cbv_eval] theorem sequence77_3_t_7_t_tail0 :
    instructionSequenceAt 63 true { bytes := artifactBytes, pos := 15606, limit := 15653 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 15608, limit := 15653 }) := by
  cbv

@[cbv_eval] theorem sequence77_3_t_17_t_tail1 :
    instructionSequenceAt 52 true { bytes := artifactBytes, pos := 15627, limit := 15653 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15628, limit := 15653 }) := by
  cbv

@[cbv_eval] theorem sequence77_3_t_17_t_tail0 :
    instructionSequenceAt 53 true { bytes := artifactBytes, pos := 15626, limit := 15653 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 15628, limit := 15653 }) := by
  cbv

@[cbv_eval] theorem sequence77_3_t_tail30 :
    instructionSequenceAt 42 true { bytes := artifactBytes, pos := 15649, limit := 15653 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15650, limit := 15653 }) := by
  cbv

@[cbv_eval] theorem sequence77_3_t_tail24 :
    instructionSequenceAt 48 true { bytes := artifactBytes, pos := 15639, limit := 15653 } =
      .ok (([Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 }], .end), { bytes := artifactBytes, pos := 15650, limit := 15653 }) := by
  cbv

@[cbv_eval] theorem sequence77_3_t_tail16 :
    instructionSequenceAt 56 true { bytes := artifactBytes, pos := 15623, limit := 15653 } =
      .ok (([Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none,
 Wasm.Binary.Instr.globalGet 3,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.globalSet 3,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 40,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 }], .end), { bytes := artifactBytes, pos := 15650, limit := 15653 }) := by
  cbv

@[cbv_eval] theorem sequence77_3_t_tail8 :
    instructionSequenceAt 64 true { bytes := artifactBytes, pos := 15608, limit := 15653 } =
      .ok (([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 40,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 1,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none,
 Wasm.Binary.Instr.globalGet 3,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.globalSet 3,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 40,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 }], .end), { bytes := artifactBytes, pos := 15650, limit := 15653 }) := by
  cbv

@[cbv_eval] theorem sequence77_3_t_tail0 :
    instructionSequenceAt 72 true { bytes := artifactBytes, pos := 15583, limit := 15653 } =
      .ok (([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 48,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.i64Const 5501223100278326855,
 Wasm.Binary.Instr.i64Ne,
 Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 40,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 1,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none,
 Wasm.Binary.Instr.globalGet 3,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.globalSet 3,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 40,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 }], .end), { bytes := artifactBytes, pos := 15650, limit := 15653 }) := by
  cbv

@[cbv_opaque] def body77Tail5 : List Instr := []

@[cbv_eval] theorem sequence77_tail5 :
    instructionSequenceAt 72 false { bytes := artifactBytes, pos := 15652, limit := 15653 } =
      .ok ((body77Tail5, .end), { bytes := artifactBytes, pos := 15653, limit := 15653 }) := by
  change _ = (Except.ok (([], .end), { bytes := artifactBytes, pos := 15653, limit := 15653 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body77Tail0 : List Instr := ([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Ne,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 48,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.i64Const 5501223100278326855,
    Wasm.Binary.Instr.i64Ne,
    Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none,
    Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 40,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 1,
    Wasm.Binary.Instr.localGet 1,
    Wasm.Binary.Instr.i64Const 0,
    Wasm.Binary.Instr.i64Eq,
    Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none,
    Wasm.Binary.Instr.globalGet 3,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.globalSet 3,
    Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 40,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.localGet 1,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i64Store { align := 3, offset := 0 }]
   none,
 Wasm.Binary.Instr.localGet 0] ++ body77Tail5)

@[cbv_eval] theorem sequence77_tail0 :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 15576, limit := 15653 } =
      .ok ((body77Tail0, .end), { bytes := artifactBytes, pos := 15653, limit := 15653 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Ne,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 48,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.i64Const 5501223100278326855,
    Wasm.Binary.Instr.i64Ne,
    Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none,
    Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 40,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 1,
    Wasm.Binary.Instr.localGet 1,
    Wasm.Binary.Instr.i64Const 0,
    Wasm.Binary.Instr.i64Eq,
    Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none,
    Wasm.Binary.Instr.globalGet 3,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.globalSet 3,
    Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 40,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.localGet 1,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i64Store { align := 3, offset := 0 }]
   none,
 Wasm.Binary.Instr.localGet 0] ++ body77Tail5), .end), { bytes := artifactBytes, pos := 15653, limit := 15653 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
