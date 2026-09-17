import Project.TinyGpt2Hidden.ArtifactBody69Part4

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence69_155_t_tail1 :
    instructionSequenceAt 808 true { bytes := artifactBytes, pos := 8815, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8816, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_155_t_tail0 :
    instructionSequenceAt 809 true { bytes := artifactBytes, pos := 8813, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Const 0], .otherwise), { bytes := artifactBytes, pos := 8816, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_155_e_tail6 :
    instructionSequenceAt 803 false { bytes := artifactBytes, pos := 8834, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8835, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_155_e_tail0 :
    instructionSequenceAt 809 false { bytes := artifactBytes, pos := 8816, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Const (-1),
 Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.i64DivU,
 Wasm.Binary.Instr.localGet 39,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])], .end), { bytes := artifactBytes, pos := 8835, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_163_t_tail1 :
    instructionSequenceAt 800 true { bytes := artifactBytes, pos := 8850, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8851, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_163_t_tail0 :
    instructionSequenceAt 801 true { bytes := artifactBytes, pos := 8849, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8851, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_163_e_tail1 :
    instructionSequenceAt 800 false { bytes := artifactBytes, pos := 8853, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8854, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_163_e_tail0 :
    instructionSequenceAt 801 false { bytes := artifactBytes, pos := 8851, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 38], .end), { bytes := artifactBytes, pos := 8854, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_173_t_tail1 :
    instructionSequenceAt 790 true { bytes := artifactBytes, pos := 8873, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8874, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_173_t_tail0 :
    instructionSequenceAt 791 true { bytes := artifactBytes, pos := 8872, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8874, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_173_e_tail1 :
    instructionSequenceAt 790 false { bytes := artifactBytes, pos := 8876, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8877, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_173_e_tail0 :
    instructionSequenceAt 791 false { bytes := artifactBytes, pos := 8874, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 35], .end), { bytes := artifactBytes, pos := 8877, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_180_t_tail11 :
    instructionSequenceAt 773 true { bytes := artifactBytes, pos := 8908, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8909, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_180_t_tail8 :
    instructionSequenceAt 776 true { bytes := artifactBytes, pos := 8903, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Add, Wasm.Binary.Instr.i32WrapI64, Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 8909, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_180_t_tail0 :
    instructionSequenceAt 784 true { bytes := artifactBytes, pos := 8890, limit := 9325 } =
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
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 8909, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_180_e_tail1 :
    instructionSequenceAt 783 false { bytes := artifactBytes, pos := 8910, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8911, limit := 9325 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
