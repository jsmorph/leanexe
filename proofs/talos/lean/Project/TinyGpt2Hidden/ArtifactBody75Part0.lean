import Project.Artifact.Binary.InstructionEvaluate
import Project.Artifact.Binary.Equality
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence75_18_t_0_t_23_t_3_t_tail2 :
    instructionSequenceAt 308 true { bytes := artifactBytes, pos := 15277, limit := 15544 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 15278, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_23_t_3_t_tail0 :
    instructionSequenceAt 310 true { bytes := artifactBytes, pos := 15273, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.localGet 5, Wasm.Binary.Instr.globalSet 1], .otherwise), { bytes := artifactBytes, pos := 15278, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_23_t_3_e_tail6 :
    instructionSequenceAt 304 false { bytes := artifactBytes, pos := 15289, limit := 15544 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15290, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_23_t_3_e_tail0 :
    instructionSequenceAt 310 false { bytes := artifactBytes, pos := 15278, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 }], .end), { bytes := artifactBytes, pos := 15290, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_23_t_tail42 :
    instructionSequenceAt 273 true { bytes := artifactBytes, pos := 15369, limit := 15544 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 15370, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_23_t_tail40 :
    instructionSequenceAt 275 true { bytes := artifactBytes, pos := 15365, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.localGet 3, Wasm.Binary.Instr.localSet 6], .otherwise), { bytes := artifactBytes, pos := 15370, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_23_t_tail32 :
    instructionSequenceAt 283 true { bytes := artifactBytes, pos := 15349, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 6], .otherwise), { bytes := artifactBytes, pos := 15370, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_23_t_tail24 :
    instructionSequenceAt 291 true { bytes := artifactBytes, pos := 15336, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 16,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 6], .otherwise), { bytes := artifactBytes, pos := 15370, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_23_t_tail16 :
    instructionSequenceAt 299 true { bytes := artifactBytes, pos := 15321, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 32,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 24,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 16,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 6], .otherwise), { bytes := artifactBytes, pos := 15370, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_23_t_tail8 :
    instructionSequenceAt 307 true { bytes := artifactBytes, pos := 15296, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.i64Const 5501223100278326855,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 40,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 32,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 24,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 16,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 6], .otherwise), { bytes := artifactBytes, pos := 15370, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_23_t_tail0 :
    instructionSequenceAt 315 true { bytes := artifactBytes, pos := 15266, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 5, Wasm.Binary.Instr.globalSet 1]
   (some [Wasm.Binary.Instr.localGet 2,
     Wasm.Binary.Instr.i64Const 8,
     Wasm.Binary.Instr.i64Sub,
     Wasm.Binary.Instr.i32WrapI64,
     Wasm.Binary.Instr.localGet 5,
     Wasm.Binary.Instr.i64Store { align := 3, offset := 0 }]),
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 48,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 5501223100278326855,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 40,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 32,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 24,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 16,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 6], .otherwise), { bytes := artifactBytes, pos := 15370, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_23_e_tail4 :
    instructionSequenceAt 311 false { bytes := artifactBytes, pos := 15378, limit := 15544 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15379, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_23_e_tail0 :
    instructionSequenceAt 315 false { bytes := artifactBytes, pos := 15370, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.localGet 3, Wasm.Binary.Instr.localSet 2, Wasm.Binary.Instr.localGet 5, Wasm.Binary.Instr.localSet 3], .end), { bytes := artifactBytes, pos := 15379, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_22_t_21_t_8_t_tail1 :
    instructionSequenceAt 304 true { bytes := artifactBytes, pos := 15445, limit := 15544 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15446, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_22_t_21_t_8_t_tail0 :
    instructionSequenceAt 305 true { bytes := artifactBytes, pos := 15444, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 15446, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_tail25 :
    instructionSequenceAt 315 false { bytes := artifactBytes, pos := 15381, limit := 15544 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15382, limit := 15544 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
