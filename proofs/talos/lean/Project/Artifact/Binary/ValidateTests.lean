import Project.Artifact.Binary.Validate

namespace Wasm.Binary.Tests

private def baseModule : RawModule :=
  { sections := [.type, .function, .memory, .code]
    types := [{ params := [], results := [] }]
    functionTypeIndices := [0]
    memories := [{ limits := { min := 1, max := none } }]
    globals := []
    exports := []
    codes := [{ locals := [], body := [] }] }

private def accepted (module_ : RawModule) : Bool :=
  match validate module_ with
  | .ok _ => true
  | .error _ => false

private def rejectedWith (module_ : RawModule) (kind : ValidationErrorKind) : Bool :=
  match validate module_ with
  | .ok _ => false
  | .error error => decide (error.kind = kind)

example : accepted baseModule = true := by native_decide

example : rejectedWith { baseModule with codes := [] }
    (.functionCodeCountMismatch 1 0) = true := by
  native_decide

example : rejectedWith { baseModule with functionTypeIndices := [1] }
    (.typeIndexOutOfBounds 1) = true := by
  native_decide

example : rejectedWith { baseModule with memories := [] } (.memoryCount 0) = true := by
  native_decide

example : rejectedWith
    { baseModule with memories := [{ limits := { min := 2, max := some 1 } }] }
    .invalidMemoryLimits = true := by
  native_decide

example : rejectedWith
    { baseModule with codes := [{ locals := [], body := [.drop] }] }
    (.stackUnderflow none) = true := by
  native_decide

example : rejectedWith
    { baseModule with
      codes := [{ locals := [], body := [.i32Const 0, .block .empty [.drop]] }] }
    (.stackUnderflow none) = true := by
  native_decide

example : rejectedWith
    { baseModule with
      codes := [{ locals := [], body := [.i32Const 0, .loop .empty [.drop]] }] }
    (.stackUnderflow none) = true := by
  native_decide

example : rejectedWith
    { baseModule with
      codes := [{ locals := [], body := [.i32Const ((2 : Int) ^ 31)] }] }
    (.constantOutOfRange 32 ((2 : Int) ^ 31)) = true := by
  native_decide

example : rejectedWith
    { baseModule with
      codes := [{ locals := [], body := [.i64Const ((2 : Int) ^ 63)] }] }
    (.constantOutOfRange 64 ((2 : Int) ^ 63)) = true := by
  native_decide

example : rejectedWith
    { baseModule with codes := [{ locals := [], body := [.br 1] }] }
    (.branchDepthOutOfBounds 1) = true := by
  native_decide

example : rejectedWith
    { baseModule with codes := [{ locals := [], body := [.localGet 0] }] }
    (.localIndexOutOfBounds 0) = true := by
  native_decide

example : rejectedWith
    { baseModule with
      sections := [.type, .function, .memory, .global, .code]
      globals :=
        [{ type := { type := .i64, mutability := .immutable }, init := .i64Const 0 }]
      codes := [{ locals := [], body := [.i64Const 0, .globalSet 0] }] }
    (.immutableGlobal 0) = true := by
  native_decide

example : rejectedWith
    { baseModule with
      types := [{ params := [], results := [.i64] }]
      codes :=
        [{ locals := [], body := [.i32Const 0, .i64Load { align := 4, offset := 0 }] }] }
    (.invalidAlignment 4 3) = true := by
  native_decide

example : accepted
    { baseModule with
      types := [{ params := [], results := [.i64] }]
      codes :=
        [{ locals := [], body :=
            [.i64Const 0, .f64ReinterpretI64,
             .i64Const 0, .f64ReinterpretI64,
             .f64Add,
             .i64Const 0, .f64ReinterpretI64,
             .f64Mul, .i64ReinterpretF64] }] } = true := by
  native_decide

example : rejectedWith
    { baseModule with
      codes := [{ locals := [], body := [.i64Const 0, .i64Const 0, .f64Add] }] }
    (.typeMismatch .f64 .i64) = true := by
  native_decide

private def duplicateExports : List Export :=
  [{ name := { bytes := [102], text := "f" }, desc := .func 0 },
   { name := { bytes := [102], text := "f" }, desc := .func 0 }]

example : rejectedWith
    { baseModule with
      sections := [.type, .function, .memory, .export, .code]
      exports := duplicateExports }
    (.duplicateExportName "f") = true := by
  native_decide

end Wasm.Binary.Tests
