import Project.TinyGpt2Hidden.ArtifactBody78Part1

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence78_39_t_tail15 :
    instructionSequenceAt 292 true { bytes := artifactBytes, pos := 15840, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15841, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_39_t_tail8 :
    instructionSequenceAt 299 true { bytes := artifactBytes, pos := 15775, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 5,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 6,
 Wasm.Binary.Instr.block
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.loop
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
       Wasm.Binary.Instr.br 0]]], .end), { bytes := artifactBytes, pos := 15841, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_39_t_tail0 :
    instructionSequenceAt 307 true { bytes := artifactBytes, pos := 15760, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 16,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 3,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 5,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 6,
 Wasm.Binary.Instr.block
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.loop
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
       Wasm.Binary.Instr.br 0]]], .end), { bytes := artifactBytes, pos := 15841, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_tail19 :
    instructionSequenceAt 284 true { bytes := artifactBytes, pos := 15971, limit := 16006 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 15972, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_tail16 :
    instructionSequenceAt 287 true { bytes := artifactBytes, pos := 15878, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 7,
 Wasm.Binary.Instr.block
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.loop
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
       Wasm.Binary.Instr.br 0]]], .end), { bytes := artifactBytes, pos := 15972, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_tail8 :
    instructionSequenceAt 295 true { bytes := artifactBytes, pos := 15862, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 4,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 5,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 7,
 Wasm.Binary.Instr.block
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.loop
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
       Wasm.Binary.Instr.br 0]]], .end), { bytes := artifactBytes, pos := 15972, limit := 16006 }) := by
  cbv

@[cbv_eval] theorem sequence78_43_t_tail0 :
    instructionSequenceAt 303 true { bytes := artifactBytes, pos := 15848, limit := 16006 } =
      .ok (([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 3,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 16,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 4,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 5,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 7,
 Wasm.Binary.Instr.block
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.loop
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
       Wasm.Binary.Instr.br 0]]], .end), { bytes := artifactBytes, pos := 15972, limit := 16006 }) := by
  cbv

@[cbv_opaque] def body78Tail62 : List Instr := []

@[cbv_eval] theorem sequence78_tail62 :
    instructionSequenceAt 286 false { bytes := artifactBytes, pos := 16005, limit := 16006 } =
      .ok ((body78Tail62, .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  change _ = (Except.ok (([], .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body78Tail56 : List Instr := ([Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.globalGet 1,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.globalSet 1] ++ body78Tail62)

@[cbv_eval] theorem sequence78_tail56 :
    instructionSequenceAt 292 false { bytes := artifactBytes, pos := 15994, limit := 16006 } =
      .ok ((body78Tail56, .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.globalGet 1,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.globalSet 1] ++ body78Tail62), .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body78Tail48 : List Instr := ([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 40,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 8] ++ body78Tail56)

@[cbv_eval] theorem sequence78_tail48 :
    instructionSequenceAt 300 false { bytes := artifactBytes, pos := 15979, limit := 16006 } =
      .ok ((body78Tail48, .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 40,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 8] ++ body78Tail56), .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body78Tail40 : List Instr := ([Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.i64Const 2,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 3,
    Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 16,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 4,
    Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 5,
    Wasm.Binary.Instr.i64Const 0,
    Wasm.Binary.Instr.localSet 7,
    Wasm.Binary.Instr.block
      (Wasm.Binary.BlockType.empty)
      [Wasm.Binary.Instr.loop
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
          Wasm.Binary.Instr.br 0]]]
   none,
 Wasm.Binary.Instr.globalGet 5,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.globalSet 5] ++ body78Tail48)

@[cbv_eval] theorem sequence78_tail40 :
    instructionSequenceAt 308 false { bytes := artifactBytes, pos := 15841, limit := 16006 } =
      .ok ((body78Tail40, .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.i64Const 2,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 3,
    Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 16,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 4,
    Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 5,
    Wasm.Binary.Instr.i64Const 0,
    Wasm.Binary.Instr.localSet 7,
    Wasm.Binary.Instr.block
      (Wasm.Binary.BlockType.empty)
      [Wasm.Binary.Instr.loop
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
          Wasm.Binary.Instr.br 0]]]
   none,
 Wasm.Binary.Instr.globalGet 5,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.globalSet 5] ++ body78Tail48), .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body78Tail32 : List Instr := ([Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 2,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 16,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 3,
    Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 5,
    Wasm.Binary.Instr.i64Const 0,
    Wasm.Binary.Instr.localSet 6,
    Wasm.Binary.Instr.block
      (Wasm.Binary.BlockType.empty)
      [Wasm.Binary.Instr.loop
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
          Wasm.Binary.Instr.br 0]]]
   none] ++ body78Tail40)

@[cbv_eval] theorem sequence78_tail32 :
    instructionSequenceAt 316 false { bytes := artifactBytes, pos := 15746, limit := 16006 } =
      .ok ((body78Tail32, .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 2,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 16,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 3,
    Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 8,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
    Wasm.Binary.Instr.localSet 5,
    Wasm.Binary.Instr.i64Const 0,
    Wasm.Binary.Instr.localSet 6,
    Wasm.Binary.Instr.block
      (Wasm.Binary.BlockType.empty)
      [Wasm.Binary.Instr.loop
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
          Wasm.Binary.Instr.br 0]]]
   none] ++ body78Tail40), .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body78Tail24 : List Instr := ([Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.globalSet 4,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 40,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.localGet 1,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
    Wasm.Binary.Instr.ret]
   none,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 24] ++ body78Tail32)

@[cbv_eval] theorem sequence78_tail24 :
    instructionSequenceAt 324 false { bytes := artifactBytes, pos := 15716, limit := 16006 } =
      .ok ((body78Tail24, .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.globalSet 4,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.empty)
   [Wasm.Binary.Instr.localGet 0,
    Wasm.Binary.Instr.i64Const 40,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i32WrapI64,
    Wasm.Binary.Instr.localGet 1,
    Wasm.Binary.Instr.i64Const 1,
    Wasm.Binary.Instr.i64Sub,
    Wasm.Binary.Instr.i64Store { align := 3, offset := 0 },
    Wasm.Binary.Instr.ret]
   none,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 24] ++ body78Tail32), .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body78Tail16 : List Instr := ([Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 1,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none,
 Wasm.Binary.Instr.globalGet 4,
 Wasm.Binary.Instr.i64Const 1] ++ body78Tail24)

@[cbv_eval] theorem sequence78_tail16 :
    instructionSequenceAt 332 false { bytes := artifactBytes, pos := 15698, limit := 16006 } =
      .ok ((body78Tail16, .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.localSet 1,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none,
 Wasm.Binary.Instr.globalGet 4,
 Wasm.Binary.Instr.i64Const 1] ++ body78Tail24), .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body78Tail8 : List Instr := ([Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.i64Const 5501223100278326855,
 Wasm.Binary.Instr.i64Ne,
 Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 40,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64] ++ body78Tail16)

@[cbv_eval] theorem sequence78_tail8 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 15673, limit := 16006 } =
      .ok ((body78Tail8, .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Load { align := 3, offset := 0 },
 Wasm.Binary.Instr.i64Const 5501223100278326855,
 Wasm.Binary.Instr.i64Ne,
 Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.unreachable] none,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 40,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64] ++ body78Tail16), .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body78Tail0 : List Instr := ([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.ret] none,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 48,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64] ++ body78Tail8)

@[cbv_eval] theorem sequence78_tail0 :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 15658, limit := 16006 } =
      .ok ((body78Tail0, .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.i64Eq,
 Wasm.Binary.Instr.iff (Wasm.Binary.BlockType.empty) [Wasm.Binary.Instr.ret] none,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.i64Const 48,
 Wasm.Binary.Instr.i64Sub,
 Wasm.Binary.Instr.i32WrapI64] ++ body78Tail8), .end), { bytes := artifactBytes, pos := 16006, limit := 16006 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
