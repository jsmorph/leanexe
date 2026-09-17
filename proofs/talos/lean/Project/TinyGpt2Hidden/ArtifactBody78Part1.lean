import Project.TinyGpt2Hidden.ArtifactBody78Part0

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence78_43_t_18_t_0_t_tail12 :
    instructionSequenceAt 269 false { bytes := artifactBytes, pos := 15969, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15970, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_18_t_0_t_tail8 :
    instructionSequenceAt 273 false { bytes := artifactBytes, pos := 15962, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.i64Const 1, Wasm.Binary.Instr.i64Add, Wasm.Binary.Instr.localSet 7, Wasm.Binary.Instr.br 0], .end), { bytes := artifactBytes, pos := 15970, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_18_t_0_t_tail0 :
    instructionSequenceAt 281 false { bytes := artifactBytes, pos := 15886, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.i64GeU,
 Wasm.Binary.Instr.brIf 1,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 6,
 Wasm.Binary.Instr.block
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.loop
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
       Wasm.Binary.Instr.br 0]],
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localSet 7,
 Wasm.Binary.Instr.br 0], .end), { bytes := artifactBytes, pos := 15970, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_39_t_14_t_tail1 :
    instructionSequenceAt 290 false { bytes := artifactBytes, pos := 15839, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15840, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_39_t_14_t_tail0 :
    instructionSequenceAt 291 false { bytes := artifactBytes, pos := 15788, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.loop
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 6,
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
    Wasm.Binary.Instr.br 0]], .end), { bytes := artifactBytes, pos := 15840, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_18_t_tail1 :
    instructionSequenceAt 282 false { bytes := artifactBytes, pos := 15970, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15971, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_18_t_tail0 :
    instructionSequenceAt 283 false { bytes := artifactBytes, pos := 15884, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.loop
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 7,
    Wasm.Binary.Instr.localGet 3,
    Wasm.Binary.Instr.i64GeU,
    Wasm.Binary.Instr.brIf 1,
    Wasm.Binary.Instr.i64Const 0,
    Wasm.Binary.Instr.localSet 6,
    Wasm.Binary.Instr.block
      (Wasm.Binary.BlockType.empty)
      [Wasm.Binary.Instr.loop
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
          Wasm.Binary.Instr.br 0]],
    Wasm.Binary.Instr.localGet 7,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Add,
    Wasm.Binary.Instr.localSet 7,
    Wasm.Binary.Instr.br 0]], .end), { bytes := artifactBytes, pos := 15971, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_3_t_tail1 :
    instructionSequenceAt 342 true { bytes := artifactBytes, pos := 15666, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15667, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_3_t_tail0 :
    instructionSequenceAt 343 true { bytes := artifactBytes, pos := 15665, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.ret], .end), { bytes := artifactBytes, pos := 15667, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_11_t_tail1 :
    instructionSequenceAt 334 true { bytes := artifactBytes, pos := 15691, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15692, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_11_t_tail0 :
    instructionSequenceAt 335 true { bytes := artifactBytes, pos := 15690, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 15692, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_21_t_tail1 :
    instructionSequenceAt 324 true { bytes := artifactBytes, pos := 15711, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15712, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_21_t_tail0 :
    instructionSequenceAt 325 true { bytes := artifactBytes, pos := 15710, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 15712, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_29_t_tail9 :
    instructionSequenceAt 308 true { bytes := artifactBytes, pos := 15741, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15742, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_29_t_tail8 :
    instructionSequenceAt 309 true { bytes := artifactBytes, pos := 15740, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.ret], .end), { bytes := artifactBytes, pos := 15742, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_29_t_tail0 :
    instructionSequenceAt 317 true { bytes := artifactBytes, pos := 15726, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 40,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.ret], .end), { bytes := artifactBytes, pos := 15742, limit := 16006 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
