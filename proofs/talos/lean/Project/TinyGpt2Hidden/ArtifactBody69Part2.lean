import Project.TinyGpt2Hidden.ArtifactBody69Part1

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence69_35_e_tail0 :
    instructionSequenceAt 929 false { bytes := artifactBytes, pos := 8452, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 8454, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_49_t_tail1 :
    instructionSequenceAt 914 true { bytes := artifactBytes, pos := 8481, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8482, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_49_t_tail0 :
    instructionSequenceAt 915 true { bytes := artifactBytes, pos := 8480, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8482, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_49_e_tail1 :
    instructionSequenceAt 914 false { bytes := artifactBytes, pos := 8484, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8485, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_49_e_tail0 :
    instructionSequenceAt 915 false { bytes := artifactBytes, pos := 8482, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 38], .end), { bytes := artifactBytes, pos := 8485, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_59_t_tail1 :
    instructionSequenceAt 904 true { bytes := artifactBytes, pos := 8504, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8505, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_59_t_tail0 :
    instructionSequenceAt 905 true { bytes := artifactBytes, pos := 8503, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8505, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_59_e_tail1 :
    instructionSequenceAt 904 false { bytes := artifactBytes, pos := 8507, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8508, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_59_e_tail0 :
    instructionSequenceAt 905 false { bytes := artifactBytes, pos := 8505, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 35], .end), { bytes := artifactBytes, pos := 8508, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_66_t_tail11 :
    instructionSequenceAt 887 true { bytes := artifactBytes, pos := 8539, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8540, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_66_t_tail8 :
    instructionSequenceAt 890 true { bytes := artifactBytes, pos := 8534, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Add, Wasm.Binary.Instr.i32WrapI64, Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 8540, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_66_t_tail0 :
    instructionSequenceAt 898 true { bytes := artifactBytes, pos := 8521, limit := 9325 } =
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
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 8540, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_66_e_tail1 :
    instructionSequenceAt 897 false { bytes := artifactBytes, pos := 8541, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8542, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_66_e_tail0 :
    instructionSequenceAt 898 false { bytes := artifactBytes, pos := 8540, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 8542, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_79_t_tail1 :
    instructionSequenceAt 884 true { bytes := artifactBytes, pos := 8569, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8570, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_79_t_tail0 :
    instructionSequenceAt 885 true { bytes := artifactBytes, pos := 8567, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Const 0], .otherwise), { bytes := artifactBytes, pos := 8570, limit := 9325 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
