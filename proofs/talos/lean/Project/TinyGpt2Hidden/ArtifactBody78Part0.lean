import Project.Artifact.Binary.InstructionEvaluate
import Project.Artifact.Binary.Equality
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence78_43_t_18_t_0_t_6_t_0_t_11_t_tail16 :
    instructionSequenceAt 242 true { bytes := artifactBytes, pos := 15948, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15949, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_18_t_0_t_6_t_0_t_11_t_tail8 :
    instructionSequenceAt 250 true { bytes := artifactBytes, pos := 15934, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Mul,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 8,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.call 78], .end), { bytes := artifactBytes, pos := 15949, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_18_t_0_t_6_t_0_t_11_t_tail0 :
    instructionSequenceAt 258 true { bytes := artifactBytes, pos := 15921, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.i64Mul,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Mul,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 8,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.call 78], .end), { bytes := artifactBytes, pos := 15949, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_18_t_0_t_6_t_0_t_tail17 :
    instructionSequenceAt 254 false { bytes := artifactBytes, pos := 15958, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15959, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_18_t_0_t_6_t_0_t_tail16 :
    instructionSequenceAt 255 false { bytes := artifactBytes, pos := 15956, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.br 0], .end), { bytes := artifactBytes, pos := 15959, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_18_t_0_t_6_t_0_t_tail8 :
    instructionSequenceAt 263 false { bytes := artifactBytes, pos := 15915, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.i64And,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Ne,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.localGet 7,
    Wasm.Binary.Instr.localGet 4,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.localGet 6,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 8,
    Wasm.Binary.Instr.localGet 8,
    Wasm.Binary.Instr.call 78]
   none,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localSet 6,
 Wasm.Binary.Instr.br 0], .end), { bytes := artifactBytes, pos := 15959, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_18_t_0_t_6_t_0_t_tail0 :
    instructionSequenceAt 271 false { bytes := artifactBytes, pos := 15901, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.i64GeU,
 Wasm.Binary.Instr.brIf 1,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.i64ShrU,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64And,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Ne,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.localGet 7,
    Wasm.Binary.Instr.localGet 4,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.localGet 6,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 8,
    Wasm.Binary.Instr.localGet 8,
    Wasm.Binary.Instr.call 78]
   none,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localSet 6,
 Wasm.Binary.Instr.br 0], .end), { bytes := artifactBytes, pos := 15959, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_39_t_14_t_0_t_11_t_tail10 :
    instructionSequenceAt 266 true { bytes := artifactBytes, pos := 15828, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15829, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_39_t_14_t_0_t_11_t_tail8 :
    instructionSequenceAt 268 true { bytes := artifactBytes, pos := 15824, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.localGet 8, Wasm.Binary.Instr.call 78], .end), { bytes := artifactBytes, pos := 15829, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_39_t_14_t_0_t_11_t_tail0 :
    instructionSequenceAt 276 true { bytes := artifactBytes, pos := 15810, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Mul,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 8,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.call 78], .end), { bytes := artifactBytes, pos := 15829, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_18_t_0_t_6_t_tail1 :
    instructionSequenceAt 272 false { bytes := artifactBytes, pos := 15959, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15960, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_18_t_0_t_6_t_tail0 :
    instructionSequenceAt 273 false { bytes := artifactBytes, pos := 15899, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.loop
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 6,
    Wasm.Binary.Instr.localGet 4,
    Wasm.Binary.Instr.i64GeU,
    Wasm.Binary.Instr.brIf 1,
    Wasm.Binary.Instr.localGet 5,
    Wasm.Binary.Instr.localGet 6,
    Wasm.Binary.Instr.i64ShrU,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64And,
    Wasm.Binary.Instr.i64Const 0,
    Wasm.Binary.Instr.i64Ne,
    Wasm.Binary.Instr.iff
      (Wasm.Binary.BlockType.empty)
      [Wasm.Binary.Instr.localGet 0,
       Wasm.Binary.Instr.i64Const 8,
       Wasm.Binary.Instr.i64Add,
       Wasm.Binary.Instr.localGet 7,
       Wasm.Binary.Instr.localGet 4,
       Wasm.Binary.Instr.i64Mul,
       Wasm.Binary.Instr.localGet 6,
       Wasm.Binary.Instr.i64Add,
       Wasm.Binary.Instr.i64Const 8,
       Wasm.Binary.Instr.i64Mul,
       Wasm.Binary.Instr.i64Add,
       Wasm.Binary.Instr.i32WrapI64,
       Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
       Wasm.Binary.Instr.localSet 8,
       Wasm.Binary.Instr.localGet 8,
       Wasm.Binary.Instr.call 78]
      none,
    Wasm.Binary.Instr.localGet 6,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.localSet 6,
    Wasm.Binary.Instr.br 0]], .end), { bytes := artifactBytes, pos := 15960, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_39_t_14_t_0_t_tail17 :
    instructionSequenceAt 272 false { bytes := artifactBytes, pos := 15838, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15839, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_39_t_14_t_0_t_tail16 :
    instructionSequenceAt 273 false { bytes := artifactBytes, pos := 15836, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.br 0], .end), { bytes := artifactBytes, pos := 15839, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_39_t_14_t_0_t_tail8 :
    instructionSequenceAt 281 false { bytes := artifactBytes, pos := 15804, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.i64And,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Ne,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.localGet 6,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 8,
    Wasm.Binary.Instr.localGet 8,
    Wasm.Binary.Instr.call 78]
   none,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localSet 6,
 Wasm.Binary.Instr.br 0], .end), { bytes := artifactBytes, pos := 15839, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_39_t_14_t_0_t_tail0 :
    instructionSequenceAt 289 false { bytes := artifactBytes, pos := 15790, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64GeU,
 Wasm.Binary.Instr.brIf 1,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.i64ShrU,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64And,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Ne,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.localGet 6,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Mul,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 8,
    Wasm.Binary.Instr.localGet 8,
    Wasm.Binary.Instr.call 78]
   none,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localSet 6,
 Wasm.Binary.Instr.br 0], .end), { bytes := artifactBytes, pos := 15839, limit := 16006 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
