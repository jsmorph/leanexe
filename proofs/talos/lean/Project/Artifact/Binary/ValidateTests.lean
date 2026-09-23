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

example : accepted
    { baseModule with
      types := [{ params := [], results := [.i64] }]
      codes := [{ locals := [], body :=
        [.i64Const 0, .f64ReinterpretI64, .i64Const 0, .f64ReinterpretI64,
         .f64Sub, .i64ReinterpretF64] }] } = true := by
  native_decide

example : rejectedWith
    { baseModule with
      codes := [{ locals := [], body := [.i64Const 0, .i64Const 0, .f64Sub] }] }
    (.typeMismatch .f64 .i64) = true := by
  native_decide

example : accepted
    { baseModule with
      types := [{ params := [], results := [.i64] }]
      codes := [{ locals := [], body :=
        [.i64Const 0, .f64ReinterpretI64, .i64Const 0, .f64ReinterpretI64,
         .f64Div, .i64ReinterpretF64] }] } = true := by
  native_decide

example : rejectedWith
    { baseModule with
      codes := [{ locals := [], body := [.i64Const 0, .i64Const 0, .f64Div] }] }
    (.typeMismatch .f64 .i64) = true := by
  native_decide

example : accepted
    { baseModule with
      types := [{ params := [], results := [.i64] }]
      codes := [{ locals := [], body :=
        [.i64Const 0, .f64ReinterpretI64, .f64Sqrt, .i64ReinterpretF64] }] } = true := by
  native_decide

example : rejectedWith
    { baseModule with
      codes := [{ locals := [], body := [.i64Const 0, .f64Sqrt] }] }
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

example : accepted
    { baseModule with
      types := [{ params := [.f32], results := [.i32] }]
      codes := [{ locals := [{ count := 1, type := .f32 }], body :=
        [.localGet 0, .localTee 1,
         .i32Const 0, .f32ReinterpretI32, .f32Add,
         .localGet 1, .f32Sub,
         .localGet 1, .f32Mul,
         .localGet 1, .f32Div,
         .block (.value .f32) [.localGet 1, .f32Sqrt], .f32Add,
         .i32ReinterpretF32] }] } = true := by
  decide +kernel

example : [.f32Add, .f32Sub, .f32Mul, .f32Div].all (fun op =>
    rejectedWith
      { baseModule with codes := [{ locals := [], body := [.i32Const 0, .i32Const 0, op] }] }
      (.typeMismatch .f32 .i32)) = true := by
  decide +kernel

example : rejectedWith
    { baseModule with codes := [{ locals := [], body := [.i64Const 0, .f32ReinterpretI32] }] }
    (.typeMismatch .i32 .i64) = true := by
  decide +kernel

example : rejectedWith
    { baseModule with codes := [{ locals := [], body := [.i32Const 0, .f32Sqrt] }] }
    (.typeMismatch .f32 .i32) = true := by
  decide +kernel

example : accepted
    { baseModule with
      types := [{ params := [], results := [.i32] }]
      codes := [{ locals := [], body := [.i32Const (-1), .i32Extend8S,
        .f32ConvertI32S, .f32Nearest, .i32TruncSatF32S] }] } = true := by
  decide +kernel

example : [.f32Nearest, .i32TruncSatF32S].all (fun op =>
    rejectedWith
      { baseModule with codes := [{ locals := [], body := [.i32Const 0, op] }] }
      (.typeMismatch .f32 .i32)) = true := by
  decide +kernel

example : [.f32ConvertI32S, .i32Extend8S].all (fun op =>
    rejectedWith
      { baseModule with codes := [{ locals := [], body := [.i64Const 0, op] }] }
      (.typeMismatch .i32 .i64)) = true := by
  decide +kernel

end Wasm.Binary.Tests
