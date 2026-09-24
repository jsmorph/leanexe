import Project.Correct.Scalar64.Pilots
import Project.Correct.Scalar64.Gcd

namespace Project.Correct.Scalar64.Pilots
open Wasm.Binary
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

def mixBytes : ByteArray := ByteArray.mk #[0, 97, 115, 109, 1, 0, 0, 0, 1, 6, 1, 96, 1, 126, 1, 126, 3, 2, 1, 0, 7, 7, 1, 3, 109, 105, 120, 0, 0, 10, 58, 1, 56, 1, 2, 126, 32, 0, 32, 0, 66, 30, 136, 133, 66, 185, 203, 147, 231, 209, 237, 145, 172, 191, 127, 126, 33, 1, 32, 1, 32, 1, 66, 27, 136, 133, 66, 235, 163, 196, 153, 177, 183, 146, 232, 148, 127, 126, 33, 2, 32, 2, 32, 2, 66, 31, 136, 133, 11]
private def mixRaw : RawModule := { sections := [Wasm.Binary.SectionId.type,                Wasm.Binary.SectionId.function,                Wasm.Binary.SectionId.export,                Wasm.Binary.SectionId.code],   types := [{ params := [Wasm.Binary.ValType.i64], results := [Wasm.Binary.ValType.i64] }],   functionTypeIndices := [0],   memories := [],   globals := [],   exports := [{ name := { bytes := [109, 105, 120], text := "mix" }, desc := Wasm.Binary.ExportDesc.func 0 }],   codes := [{ locals := [{ count := 2, type := Wasm.Binary.ValType.i64 }],               body := [Wasm.Binary.Instr.localGet 0,                        Wasm.Binary.Instr.localGet 0,                        Wasm.Binary.Instr.i64Const 30,                        Wasm.Binary.Instr.i64ShrU,                        Wasm.Binary.Instr.i64Xor,                        Wasm.Binary.Instr.i64Const (-4658895280553007687),                        Wasm.Binary.Instr.i64Mul,                        Wasm.Binary.Instr.localSet 1,                        Wasm.Binary.Instr.localGet 1,                        Wasm.Binary.Instr.localGet 1,                        Wasm.Binary.Instr.i64Const 27,                        Wasm.Binary.Instr.i64ShrU,                        Wasm.Binary.Instr.i64Xor,                        Wasm.Binary.Instr.i64Const (-7723592293110705685),                        Wasm.Binary.Instr.i64Mul,                        Wasm.Binary.Instr.localSet 2,                        Wasm.Binary.Instr.localGet 2,                        Wasm.Binary.Instr.localGet 2,                        Wasm.Binary.Instr.i64Const 31,                        Wasm.Binary.Instr.i64ShrU,                        Wasm.Binary.Instr.i64Xor] }] }
private theorem mixDecoded : decode mixBytes = .ok mixRaw := by cbv
private theorem mixValidated : Validator.validateRaw mixRaw = .ok () := by rfl
private theorem mixTranslated : Translation.module mixRaw = mixCertificate.module := by rfl

theorem mixClosed : Artifact mixCertificate mixBytes :=
  Artifact.of_parts _ mixDecoded mixValidated mixTranslated

#print axioms mixClosed
end Project.Correct.Scalar64.Pilots
