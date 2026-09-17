import Project.TinyGpt2Hidden.ArtifactBody69Part5

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence69_180_e_tail0 :
    instructionSequenceAt 784 false { bytes := artifactBytes, pos := 8909, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 8911, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_193_t_tail1 :
    instructionSequenceAt 770 true { bytes := artifactBytes, pos := 8938, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8939, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_193_t_tail0 :
    instructionSequenceAt 771 true { bytes := artifactBytes, pos := 8936, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Const 0], .otherwise), { bytes := artifactBytes, pos := 8939, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_193_e_tail6 :
    instructionSequenceAt 765 false { bytes := artifactBytes, pos := 8957, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8958, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_193_e_tail0 :
    instructionSequenceAt 771 false { bytes := artifactBytes, pos := 8939, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Const (-1),
 Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.i64DivU,
 Wasm.Binary.Instr.localGet 39,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])], .end), { bytes := artifactBytes, pos := 8958, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_201_t_tail1 :
    instructionSequenceAt 762 true { bytes := artifactBytes, pos := 8973, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8974, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_201_t_tail0 :
    instructionSequenceAt 763 true { bytes := artifactBytes, pos := 8972, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8974, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_201_e_tail1 :
    instructionSequenceAt 762 false { bytes := artifactBytes, pos := 8976, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8977, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_201_e_tail0 :
    instructionSequenceAt 763 false { bytes := artifactBytes, pos := 8974, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 38], .end), { bytes := artifactBytes, pos := 8977, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_211_t_tail1 :
    instructionSequenceAt 752 true { bytes := artifactBytes, pos := 8996, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8997, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_211_t_tail0 :
    instructionSequenceAt 753 true { bytes := artifactBytes, pos := 8995, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8997, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_211_e_tail1 :
    instructionSequenceAt 752 false { bytes := artifactBytes, pos := 8999, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 9000, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_211_e_tail0 :
    instructionSequenceAt 753 false { bytes := artifactBytes, pos := 8997, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 35], .end), { bytes := artifactBytes, pos := 9000, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_218_t_tail11 :
    instructionSequenceAt 735 true { bytes := artifactBytes, pos := 9031, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 9032, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_218_t_tail8 :
    instructionSequenceAt 738 true { bytes := artifactBytes, pos := 9026, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Add, Wasm.Binary.Instr.i32WrapI64, Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 9032, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_218_t_tail0 :
    instructionSequenceAt 746 true { bytes := artifactBytes, pos := 9013, limit := 9325 } =
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
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 9032, limit := 9325 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
