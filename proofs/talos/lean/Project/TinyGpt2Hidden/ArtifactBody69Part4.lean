import Project.TinyGpt2Hidden.ArtifactBody69Part3

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence69_117_t_tail0 :
    instructionSequenceAt 847 true { bytes := artifactBytes, pos := 8690, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Const 0], .otherwise), { bytes := artifactBytes, pos := 8693, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_117_e_tail6 :
    instructionSequenceAt 841 false { bytes := artifactBytes, pos := 8711, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8712, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_117_e_tail0 :
    instructionSequenceAt 847 false { bytes := artifactBytes, pos := 8693, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Const (-1),
 Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.i64DivU,
 Wasm.Binary.Instr.localGet 39,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])], .end), { bytes := artifactBytes, pos := 8712, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_125_t_tail1 :
    instructionSequenceAt 838 true { bytes := artifactBytes, pos := 8727, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8728, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_125_t_tail0 :
    instructionSequenceAt 839 true { bytes := artifactBytes, pos := 8726, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8728, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_125_e_tail1 :
    instructionSequenceAt 838 false { bytes := artifactBytes, pos := 8730, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8731, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_125_e_tail0 :
    instructionSequenceAt 839 false { bytes := artifactBytes, pos := 8728, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 38], .end), { bytes := artifactBytes, pos := 8731, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_135_t_tail1 :
    instructionSequenceAt 828 true { bytes := artifactBytes, pos := 8750, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8751, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_135_t_tail0 :
    instructionSequenceAt 829 true { bytes := artifactBytes, pos := 8749, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8751, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_135_e_tail1 :
    instructionSequenceAt 828 false { bytes := artifactBytes, pos := 8753, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8754, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_135_e_tail0 :
    instructionSequenceAt 829 false { bytes := artifactBytes, pos := 8751, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 35], .end), { bytes := artifactBytes, pos := 8754, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_142_t_tail11 :
    instructionSequenceAt 811 true { bytes := artifactBytes, pos := 8785, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8786, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_142_t_tail8 :
    instructionSequenceAt 814 true { bytes := artifactBytes, pos := 8780, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Add, Wasm.Binary.Instr.i32WrapI64, Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 8786, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_142_t_tail0 :
    instructionSequenceAt 822 true { bytes := artifactBytes, pos := 8767, limit := 9325 } =
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
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 8786, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_142_e_tail1 :
    instructionSequenceAt 821 false { bytes := artifactBytes, pos := 8787, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8788, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_142_e_tail0 :
    instructionSequenceAt 822 false { bytes := artifactBytes, pos := 8786, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 8788, limit := 9325 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
