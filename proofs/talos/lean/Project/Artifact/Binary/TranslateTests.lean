import Project.Artifact.Binary.Translate

namespace Wasm.Binary.Tests

example : Instr.toTalos (.block (.value .i64) []) =
    [.block 0 1 [] [] [.i64]] := by
  rfl

example : Instr.toTalos (.loop .empty []) =
    [.loop 0 0 [] [] []] := by
  rfl

example : Instr.toTalos (.iff (.value .i32) [] none) =
    [.iff 0 1 [] [] [] [.i32]] := by
  rfl

example : Instr.toTalos (.localTee 7) = [.localTee 7] := by
  rfl

private def typedRaw : RawModule :=
  { sections := []
    types := [{ params := [.i32], results := [.i64] }]
    functionTypeIndices := []
    memories := []
    globals := []
    exports := []
    codes := [] }

private def emptyCode : Code :=
  { locals := [], body := [] }

example : (Translation.functionToTalos typedRaw 0 emptyCode).typeIdx = some 0 := by
  rfl

end Wasm.Binary.Tests
