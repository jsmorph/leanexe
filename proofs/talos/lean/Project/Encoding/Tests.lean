import Project.Encoding.Examples
import Project.Gcd.Program
import Project.F64MulBits.Program
import Project.Validate.Program

namespace Wasm.Encoding.Tests

#guard unsigned 32 0 = [0]
#guard unsigned 32 127 = [127]
#guard unsigned 32 128 = [128, 1]
#guard unsigned 32 (2 ^ 32 - 1) = [255, 255, 255, 255, 15]
#guard (u32 (2 ^ 32)).isOk = false
#guard signed 32 (-1) = [127]
#guard signed 32 (-64) = [64]
#guard signed 32 (-65) = [191, 127]
#guard signed 32 63 = [63]
#guard signed 32 64 = [192, 0]
#guard signed 32 (-(2 ^ 31)) = [128, 128, 128, 128, 120]
#guard signed 64 (-(2 ^ 63)) = [128, 128, 128, 128, 128, 128, 128, 128, 128, 127]
#guard signed 64 (2 ^ 63 - 1) = [255, 255, 255, 255, 255, 255, 255, 255, 255, 0]
#guard (instruction (.localGet (2 ^ 32))).isOk = false
#guard (instruction (.block 1 0 [] [.i64] [])).isOk = false
#guard (instruction (.block 0 1 [] [] [])).isOk = false
#guard (global { init := .i32 7, declaredType := some .i32,
                 sourceInit := some [.const 8] }).isOk = false

abbrev Case := String × Wasm.Function

def fixture (cases : List Case) : Wasm.Module :=
  let types := cases.map (fun c => Spec.signature c.2)
  { funcs := cases.mapIdx (fun index c => { c.2 with typeIdx := some index })
    exports := cases.mapIdx (fun index c => { name := c.1, funcIdx := index })
    types := types
    gcTypes := types.map (fun type => { comp := .func type })
    memory := some { pagesMin := 1, pagesMax := some 2 }
    globals := [{ init := .i64 9, declaredType := some .i64, sourceInit := some [.constI64 9] },
      { init := .i32 4294967295, declaredType := some .i32, isMut := false,
        sourceInit := some [.const 4294967295] }]
    memoryExports := [("memory", 0)]
    globalExports := [("counter", 0)] }

def boundaries : Wasm.Module := fixture [
  ("min32", { results := [.i32], body := [.const 2147483648] }),
  ("minus1", { results := [.i32], body := [.const 4294967295] }),
  ("min64", { results := [.i64], body := [.constI64 9223372036854775808] }),
  ("max64", { results := [.i64], body := [.constI64 9223372036854775807] }),
  ("λ雪", { results := [.i64], body := [.constI64 42] }),
  ("nested", { params := [.i64], results := [.i64],
               body := [.localGet 0, .eqzI64,
      .iff 0 1 [.constI64 18446744073709551551] [.localGet 0] [] [.i64]] }),
  ("memory64", { results := [.i64], body := [
    .const 0, .constI64 9223372036854775808, .store64 8, .const 0, .load64 8] }),
  ("memory8", { results := [.i32], body := [
    .const 0, .const 511, .store8 1, .const 0, .load8U 1] }),
  ("globals", { results := [.i64], body := [
    .globalGet 0, .constI64 1, .addI64, .globalSet 0, .globalGet 0] }),
  ("global32", { results := [.i32], body := [.globalGet 1] }),
  ("memoryGrow", { results := [.i32], body := [.const 1, .memoryGrow, .drop, .memorySize] }),
  ("promote", { results := [.i64], body := [
    .const 1065353216, .f32ReinterpretI32, .f64PromoteF32, .i64ReinterpretF64] }),
  ("demote", { results := [.i32], body := [
    .constI64 4607182418800017408, .f64ReinterpretI64, .f32DemoteF64, .i32ReinterpretF32] }),
  ("saturate", { results := [.i32], body := [
    .const 2139095040, .f32ReinterpretI32, .i32TruncSatF32S] })]

def multipleResults : Wasm.Module :=
  let type : Wasm.FuncType := { results := [.i64, .i32] }
  let types : List Wasm.FuncType := [{ params := [.f64], results := [.f32] }, type, type]
  { funcs := [{ results := type.results, typeIdx := some 2,
                locals := [.i32, .i64, .f32, .f64, .i32],
                body := [.constI64 18446744073709551615, .const 2147483648] }]
    exports := [{ name := "pair", funcIdx := 0 }]
    types := types
    gcTypes := types.map (fun t => { comp := .func t }) }

def wasi : Wasm.Module :=
  let types : List Wasm.FuncType := [{ params := [.i32] }, {}, { params := [.i32] }]
  { types := types
    gcTypes := types.map (fun t => { comp := .func t })
    imports := [{ module := "wasi_snapshot_preview1", name := "proc_exit", params := [.i32] }]
    funcs := [{ typeIdx := some 1, body := [.const 0, .call 0] }]
    exports := [{ name := "_start", funcIdx := 1 }]
    memory := some { pagesMin := 1 }
    memoryExports := [("memory", 0)] }

def numericCases : List Case :=
  let i32 : List Wasm.Instruction := [.eq, .ltU, .gtU, .leU, .geU, .add, .and]
  let i64 : List Wasm.Instruction := [.eqI64, .neI64, .ltUI64, .leUI64, .geUI64, .addI64, .subI64, .mulI64,
    .divUI64, .remUI64, .andI64, .orI64, .xorI64, .shlI64, .shrUI64]
  let f32 : List Wasm.Instruction := [.f32Add, .f32Sub, .f32Mul, .f32Div]
  let f64 : List Wasm.Instruction := [.f64Add, .f64Sub, .f64Mul, .f64Div]
  (i32.mapIdx fun n op => (s!"i32_{n}", { results := [.i32], body := [.const 9, .const 2, op] })) ++
  (i64.mapIdx fun n op => (s!"i64_{n}", { results := [if n < 5 then .i32 else .i64], body := [.constI64 9, .constI64 2, op] })) ++
  (f32.mapIdx fun n op => (s!"f32_{n}", { results := [.i32], body := [.const 1065353216, .f32ReinterpretI32,
    .const 1073741824, .f32ReinterpretI32, op, .i32ReinterpretF32] })) ++
  (f64.mapIdx fun n op => (s!"f64_{n}", { results := [.i64], body := [.constI64 4607182418800017408,
    .f64ReinterpretI64, .constI64 4611686018427387904, .f64ReinterpretI64, op, .i64ReinterpretF64] })) ++
  [("unary32", { body := [.const 255, .extend8S, .f32ConvertI32S, .f32Nearest,
    .f32Sqrt, .i32ReinterpretF32, .eqz, .drop] }),
   ("unary64", { body := [.constI64 4616189618054758400, .f64ReinterpretI64,
    .f64Sqrt, .i64ReinterpretF64, .eqzI64, .drop] }),
   ("local", { locals := [.i32], body := [.const 7, .localTee 0, .localSet 0,
    .localGet 0, .extendUI32, .wrapI64, .drop, .nop, .ret, .unreachable] }),
   ("memory32", { body := [.const 0, .const 7, .store32 0, .const 0, .load32 0, .drop] })]

#guard (encode { wasi with funcs := [{ typeIdx := some 0, body := [] }] }).isOk = false
#guard (encode { wasi with gcTypes := [] }).isOk = false

def emit (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for (name, m) in [
      ("gcd", Project.Gcd.module), ("float", Project.F64MulBits.module),
      ("validate", Project.Validate.module), ("boundaries", boundaries),
      ("multiple", multipleResults), ("wasi", wasi), ("numeric", fixture numericCases)] do
    writeModule (directory / s!"{name}.wasm") m

end Wasm.Encoding.Tests

def main (args : List String) : IO Unit := do
  match args with
  | [directory] => Wasm.Encoding.Tests.emit directory
  | _ => throw (IO.userError "expected an output directory")
