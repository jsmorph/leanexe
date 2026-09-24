import Project.Correct.Scalar64.Pilots
import Project.Correct.Scalar64.Gcd

namespace Project.Correct.Scalar64.Pilots
open Wasm.Binary
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

def affineBytes : ByteArray := ByteArray.mk #[0, 97, 115, 109, 1, 0, 0, 0, 1, 7, 1, 96, 2, 126, 126, 1, 126, 3, 2, 1, 0, 7, 10, 1, 6, 97, 102, 102, 105, 110, 101, 0, 0, 10, 18, 1, 16, 0, 32, 0, 66, 3, 126, 32, 1, 66, 2, 126, 124, 66, 7, 124, 11]
private def affineRaw : RawModule := { sections := [Wasm.Binary.SectionId.type,                Wasm.Binary.SectionId.function,                Wasm.Binary.SectionId.export,                Wasm.Binary.SectionId.code],   types := [{ params := [Wasm.Binary.ValType.i64, Wasm.Binary.ValType.i64], results := [Wasm.Binary.ValType.i64] }],   functionTypeIndices := [0],   memories := [],   globals := [],   exports := [{ name := { bytes := [97, 102, 102, 105, 110, 101], text := "affine" },                 desc := Wasm.Binary.ExportDesc.func 0 }],   codes := [{ locals := [],               body := [Wasm.Binary.Instr.localGet 0,                        Wasm.Binary.Instr.i64Const 3,                        Wasm.Binary.Instr.i64Mul,                        Wasm.Binary.Instr.localGet 1,                        Wasm.Binary.Instr.i64Const 2,                        Wasm.Binary.Instr.i64Mul,                        Wasm.Binary.Instr.i64Add,                        Wasm.Binary.Instr.i64Const 7,                        Wasm.Binary.Instr.i64Add] }] }
private theorem affineDecoded : decode affineBytes = .ok affineRaw := by cbv
private theorem affineValidated : Validator.validateRaw affineRaw = .ok () := by rfl
private theorem affineTranslated : Translation.module affineRaw = affineCertificate.module := by rfl

theorem affineClosed : Artifact affineCertificate affineBytes :=
  Artifact.of_parts _ affineDecoded affineValidated affineTranslated

#print axioms affineClosed
end Project.Correct.Scalar64.Pilots
