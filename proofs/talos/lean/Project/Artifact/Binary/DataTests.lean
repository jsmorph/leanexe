import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Validate
import Project.Artifact.Binary.Translate
import Project.Artifact.Binary.Equality
import Lean.Elab.Tactic.Cbv

namespace Wasm.Binary.Tests

private def dataBytes : ByteArray :=
  [0, 97, 115, 109, 1, 0, 0, 0,
   5, 3, 1, 0, 1,
   11, 8, 1, 0, 65, 16, 11, 2, 42, 43].toByteArray

private def dataRaw : RawModule :=
  { sections := [.memory, .data]
    types := [], functionTypeIndices := [], globals := [], exports := [], codes := []
    memories := [{ limits := { min := 1, max := none } }]
    data := [{ offset := .i32Const 16, bytes := [42, 43] }] }

example : decode dataBytes = .ok dataRaw := by cbv

example : Validator.validateRaw dataRaw = .ok () := by decide +kernel

example : CoreValid dataRaw := Proof.validateRaw_sound (by decide +kernel)

example : (Translation.module dataRaw).memory =
    some { pagesMin := 1
           data := [{ offset := some 16, bytes := [42, 43], offsetType := some .i32 }] } := by rfl

example : ((Translation.module dataRaw).initialStore (α := Unit)).mem.read8 16 = 42 := by
  decide +kernel

example : Parser.runAll dataSegment [0, 65, 0, 11, 2, 42].toByteArray =
    .error { offset := 5, kind := .unexpectedEnd } := by decide +kernel

example : Parser.runAll dataSegment [1, 0].toByteArray =
    .error { offset := 1, kind := .malformed "unsupported data segment mode" } := by
  decide +kernel

example : Validator.validateRaw
    { dataRaw with data := [{ offset := .i64Const 16, bytes := [] }] } =
    .error { functionIndex := none, instructionPath := [], kind := .dataOffsetType } := by
  decide +kernel

example : Validator.validateRaw { dataRaw with sections := [.memory] } =
    .error { functionIndex := none, instructionPath := [], kind := .missingSection .data } := by
  decide +kernel

example : Equality.rawModuleEqual 1 dataRaw
    { dataRaw with data := [{ offset := .i32Const 16, bytes := [42, 44] }] } = false := by
  decide +kernel

#print axioms Proof.decode_sound
#print axioms Proof.validate_sound
#print axioms Equality.rawModuleEqual_sound

end Wasm.Binary.Tests
