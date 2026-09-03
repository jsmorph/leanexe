import Project.Artifact.Binary.Translate

namespace Wasm.Binary.Tests

example : ValType.toTalos .f64 = .f64 := by
  simp [ValType.toTalos]

example : Instr.toTalos (.block (.value .i64) []) =
    [.block 0 1 [] [] [.i64]] := by
  simp [Instr.toTalos, Instr.listToTalos, Translation.resultArity,
    Translation.resultTypes, ValType.toTalos]

example : Instr.toTalos (.loop .empty []) =
    [.loop 0 0 [] [] []] := by
  simp [Instr.toTalos, Instr.listToTalos, Translation.resultArity,
    Translation.resultTypes]

example : Instr.toTalos (.iff (.value .i32) [] none) =
    [.iff 0 1 [] [] [] [.i32]] := by
  simp [Instr.toTalos, Instr.listToTalos, Translation.resultArity,
    Translation.resultTypes, ValType.toTalos]

example : Instr.toTalos (.localTee 7) = [.localTee 7] := by
  simp [Instr.toTalos]

example : Instr.toTalos .f64Add = [.f64Add] := by
  simp [Instr.toTalos]

example : Instr.toTalos .f64Mul = [.f64Mul] := by
  simp [Instr.toTalos]

example : Instr.toTalos .i64ReinterpretF64 = [.i64ReinterpretF64] := by
  simp [Instr.toTalos]

example : Instr.toTalos .f64ReinterpretI64 = [.f64ReinterpretI64] := by
  simp [Instr.toTalos]

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

private def metadataRaw : RawModule :=
  { typedRaw with
    memories := [{ limits := { min := 1, max := some 2 } }]
    globals :=
      [{ type := { type := .i64, mutability := .immutable }, init := .i64Const 7 }]
    exports :=
      [{ name := { bytes := [], text := "counter" }, desc := .global 0 },
       { name := { bytes := [], text := "memory" }, desc := .memory 0 }] }

example :
    (Translation.module metadataRaw).globals =
      [{ init := .i64 7, declaredType := some .i64, isMut := false,
         sourceInit := some [.constI64 7] }] ∧
    (Translation.module metadataRaw).gcTypes =
      [{ comp := .func { params := [.i32], results := [.i64] } }] ∧
    (Translation.module metadataRaw).globalExports = [("counter", 0)] ∧
    (Translation.module metadataRaw).memoryExports = [("memory", 0)] := by
  simp [Translation.module, Translation.globals, Translation.gcTypes,
    Translation.globalExports, Translation.memoryExports, metadataRaw, typedRaw,
    Translation.globalValue, Mutability.toTalos, ConstExpr.toTalos,
    FuncType.toTalos, ValType.toTalos]
  decide

end Wasm.Binary.Tests
