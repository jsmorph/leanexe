import Project.TinyGpt2Hidden.ArtifactBody75Part0

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence75_18_t_0_t_tail24 :
    instructionSequenceAt 316 false { bytes := artifactBytes, pos := 15379, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.br 0], .end), { bytes := artifactBytes, pos := 15382, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_tail16 :
    instructionSequenceAt 324 false { bytes := artifactBytes, pos := 15252, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 5,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64GeU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 2,
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
    Wasm.Binary.Instr.localSet 6]
   (some [Wasm.Binary.Instr.localGet 3,
     Wasm.Binary.Instr.localSet 2,
     Wasm.Binary.Instr.localGet 5,
     Wasm.Binary.Instr.localSet 3]),
 Wasm.Binary.Instr.br 0], .end), { bytes := artifactBytes, pos := 15382, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_tail8 :
    instructionSequenceAt 332 false { bytes := artifactBytes, pos := 15237, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 32,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 4,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 5,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64GeU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 2,
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
    Wasm.Binary.Instr.localSet 6]
   (some [Wasm.Binary.Instr.localGet 3,
     Wasm.Binary.Instr.localSet 2,
     Wasm.Binary.Instr.localGet 5,
     Wasm.Binary.Instr.localSet 3]),
 Wasm.Binary.Instr.br 0], .end), { bytes := artifactBytes, pos := 15382, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_0_t_tail0 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 15223, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.brIf 1,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Ne,
 Wasm.Binary.Instr.brIf 1,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 32,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 4,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 5,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64GeU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 2,
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
    Wasm.Binary.Instr.localSet 6]
   (some [Wasm.Binary.Instr.localGet 3,
     Wasm.Binary.Instr.localSet 2,
     Wasm.Binary.Instr.localGet 5,
     Wasm.Binary.Instr.localSet 3]),
 Wasm.Binary.Instr.br 0], .end), { bytes := artifactBytes, pos := 15382, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_22_t_8_t_tail1 :
    instructionSequenceAt 327 true { bytes := artifactBytes, pos := 15406, limit := 15544 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15407, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_22_t_8_t_tail0 :
    instructionSequenceAt 328 true { bytes := artifactBytes, pos := 15405, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 15407, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_22_t_21_t_tail9 :
    instructionSequenceAt 306 true { bytes := artifactBytes, pos := 15446, limit := 15544 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15447, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_22_t_21_t_tail8 :
    instructionSequenceAt 307 true { bytes := artifactBytes, pos := 15442, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none], .end), { bytes := artifactBytes, pos := 15447, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_22_t_21_t_tail0 :
    instructionSequenceAt 315 true { bytes := artifactBytes, pos := 15430, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.memorySize 0,
 Wasm.Binary.Instr.i64ExtendI32U,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.memoryGrow 0,
 Wasm.Binary.Instr.i32Const (-1),
 Wasm.Binary.Instr.i32Eq,
 Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none], .end), { bytes := artifactBytes, pos := 15447, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_11_t_tail2 :
    instructionSequenceAt 347 true { bytes := artifactBytes, pos := 15206, limit := 15544 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15207, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_11_t_tail0 :
    instructionSequenceAt 349 true { bytes := artifactBytes, pos := 15202, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.i64Const 8, Wasm.Binary.Instr.localSet 1], .end), { bytes := artifactBytes, pos := 15207, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_tail1 :
    instructionSequenceAt 341 false { bytes := artifactBytes, pos := 15382, limit := 15544 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15383, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_18_t_tail0 :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 15221, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.loop
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 3,
    Wasm.Binary.Instr.i64Const 0,
    Wasm.Binary.Instr.i64Eq,
    Wasm.Binary.Instr.brIf 1,
    Wasm.Binary.Instr.localGet 6,
    Wasm.Binary.Instr.i64Const 0,
    Wasm.Binary.Instr.i64Ne,
    Wasm.Binary.Instr.brIf 1,
    Wasm.Binary.Instr.localGet 3,
    Wasm.Binary.Instr.i64Const 32,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 4,
    Wasm.Binary.Instr.localGet 3,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 5,
    Wasm.Binary.Instr.localGet 4,
    Wasm.Binary.Instr.localGet 1,
    Wasm.Binary.Instr.i64GeU,
    Wasm.Binary.Instr.iff
      (Wasm.Binary.BlockType.empty)
      [Wasm.Binary.Instr.localGet 2,
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
       Wasm.Binary.Instr.localSet 6]
      (some [Wasm.Binary.Instr.localGet 3,
        Wasm.Binary.Instr.localSet 2,
        Wasm.Binary.Instr.localGet 5,
        Wasm.Binary.Instr.localSet 3]),
    Wasm.Binary.Instr.br 0]], .end), { bytes := artifactBytes, pos := 15383, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_22_t_tail64 :
    instructionSequenceAt 274 true { bytes := artifactBytes, pos := 15533, limit := 15544 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15534, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_22_t_tail56 :
    instructionSequenceAt 282 true { bytes := artifactBytes, pos := 15517, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 }], .end), { bytes := artifactBytes, pos := 15534, limit := 15544 }) := by
  cbv

@[cbv_eval] theorem sequence75_22_t_tail48 :
    instructionSequenceAt 290 true { bytes := artifactBytes, pos := 15504, limit := 15544 } =
      .ok (([Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.i64Const 16,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 }], .end), { bytes := artifactBytes, pos := 15534, limit := 15544 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
