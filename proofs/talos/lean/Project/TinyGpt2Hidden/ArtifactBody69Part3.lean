import Project.TinyGpt2Hidden.ArtifactBody69Part2

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence69_79_e_tail6 :
    instructionSequenceAt 879 false { bytes := artifactBytes, pos := 8588, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8589, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_79_e_tail0 :
    instructionSequenceAt 885 false { bytes := artifactBytes, pos := 8570, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Const (-1),
 Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.i64DivU,
 Wasm.Binary.Instr.localGet 39,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])], .end), { bytes := artifactBytes, pos := 8589, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_87_t_tail1 :
    instructionSequenceAt 876 true { bytes := artifactBytes, pos := 8604, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8605, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_87_t_tail0 :
    instructionSequenceAt 877 true { bytes := artifactBytes, pos := 8603, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8605, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_87_e_tail1 :
    instructionSequenceAt 876 false { bytes := artifactBytes, pos := 8607, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8608, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_87_e_tail0 :
    instructionSequenceAt 877 false { bytes := artifactBytes, pos := 8605, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 38], .end), { bytes := artifactBytes, pos := 8608, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_97_t_tail1 :
    instructionSequenceAt 866 true { bytes := artifactBytes, pos := 8627, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8628, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_97_t_tail0 :
    instructionSequenceAt 867 true { bytes := artifactBytes, pos := 8626, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8628, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_97_e_tail1 :
    instructionSequenceAt 866 false { bytes := artifactBytes, pos := 8630, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8631, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_97_e_tail0 :
    instructionSequenceAt 867 false { bytes := artifactBytes, pos := 8628, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 35], .end), { bytes := artifactBytes, pos := 8631, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_104_t_tail11 :
    instructionSequenceAt 849 true { bytes := artifactBytes, pos := 8662, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8663, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_104_t_tail8 :
    instructionSequenceAt 852 true { bytes := artifactBytes, pos := 8657, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Add, Wasm.Binary.Instr.i32WrapI64, Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 8663, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_104_t_tail0 :
    instructionSequenceAt 860 true { bytes := artifactBytes, pos := 8644, limit := 9325 } =
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
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 8663, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_104_e_tail1 :
    instructionSequenceAt 859 false { bytes := artifactBytes, pos := 8664, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8665, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_104_e_tail0 :
    instructionSequenceAt 860 false { bytes := artifactBytes, pos := 8663, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 8665, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_117_t_tail1 :
    instructionSequenceAt 846 true { bytes := artifactBytes, pos := 8692, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8693, limit := 9325 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
