import Project.Compiler.ScalarLowering
import LeanExe.Wasm.Binary

namespace Project.EncodingGcd

open Wasm
open LeanExe.Wasm.Binary.CoreWasm

private def translate (label : String) (code : List LeanExe.Wasm.Instr) :
    Except String Wasm.Program :=
  match Project.Compiler.ScalarLowering.program code with
  | some result => .ok result
  | none => .error s!"unsupported instruction in {label}"

def fromIR (ir : LeanExe.IR.Module) : Except String Wasm.Module := do
  let func ← match ir.funcs.toList with
    | [func] => .ok func
    | _ => .error "expected one compiled GCD function"
  let exportName ← match func.exportName with
    | some name => .ok name
    | none => .error "compiled GCD function has no export"
  let user ← translate "GCD" (emitFuncInstrs 4 func)
  let alloc ← translate "alloc" coreAllocInstrs
  let reset ← translate "reset" coreResetInstrs
  let retain ← translate "retain" coreRetainInstrs
  let release ← translate "release" (coreReleaseInstrs 4)
  let userType : Wasm.FuncType :=
    { params := List.replicate func.params .i64
      results := List.replicate func.results.length .i64 }
  let types : List Wasm.FuncType :=
    [userType,
     { params := [.i64], results := [.i64] },
     { params := [], results := [] },
     { params := [.i64], results := [.i64] },
     { params := [.i64], results := [] }]
  let userDef : Wasm.Function :=
    { params := userType.params
      locals := List.replicate (func.locals - func.params + funcScratch func) .i64
      body := user
      results := userType.results
      typeIdx := some 0 }
  let runtime : List Wasm.Function :=
    [{ params := [.i64], locals := List.replicate 6 .i64,
       body := alloc, results := [.i64], typeIdx := some 1 },
     { params := [], locals := [], body := reset, results := [], typeIdx := some 2 },
     { params := [.i64], locals := [.i64],
       body := retain, results := [.i64], typeIdx := some 3 },
     { params := [.i64], locals := List.replicate 8 .i64,
       body := release, results := [], typeIdx := some 4 }]
  let globals : List Wasm.GlobalDecl :=
    imageGlobals.toList.map fun global =>
      { init := .i64 global.initial
        declaredType := some .i64
        isMut := global.mutable_
        sourceInit := some [.constI64 global.initial] }
  return {
    funcs := userDef :: runtime
    exports :=
      [{ name := exportName, funcIdx := 0 },
       { name := "alloc", funcIdx := 1 },
       { name := "reset", funcIdx := 2 },
       { name := "retain", funcIdx := 3 },
       { name := "release", funcIdx := 4 },
       { name := "free", funcIdx := 4 }]
    memory := some { pagesMin := 16 }
    globals := globals
    types := types
    gcTypes := types.map fun type => { comp := .func type }
    globalExports :=
      [("allocCount", 2), ("retainCount", 3),
       ("releaseCount", 4), ("freeCount", 5)]
    memoryExports := [("memory", 0)] }

end Project.EncodingGcd
