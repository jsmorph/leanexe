import LeanExe.Extract.ScalarEntryCorrectness
import LeanExe.Wasm.ArithmeticBounds

namespace LeanExe.Extract.Arithmetic

open Lean
open LeanExe.Extract.Core

/-- Strict arithmetic admission followed by the existing production compiler.
Unsupported declarations and exceeded binary format limits produce errors. -/
def compileEnvironment (env : Environment) (moduleName entry : Name) : Except String LeanExe.IR.Module := do
  let some info := env.find? entry
    | .error s!"unknown arithmetic entry: {entry}"
  if info.isUnsafe || info.isPartial then
    .error "arithmetic mode requires a safe, total declaration"
  else
    let some source := info.value?
      | .error "arithmetic entry has no executable body"
    let exportName := shortExportName entry
    if reservedExportNames.contains exportName then
      .error s!"entry export name is reserved by the runtime ABI: {exportName}"
    else
      let some func := extractScalarFunc entry (some exportName) info.type source
        | .error "unsupported arithmetic source: expected UInt64 arguments and result, literals, and the supported arithmetic operators"
      if LeanExe.Wasm.ArithmeticBounds.Fits func exportName then
        Core.compileEnvironment env moduleName entry
      else
        .error "arithmetic source exceeds WebAssembly binary format limits"

def compile (moduleText entryText : String) : IO LeanExe.IR.Module := do
  let moduleName := LeanExe.Extract.Env.parseName moduleText
  let entry := LeanExe.Extract.Env.parseName entryText
  let env ← LeanExe.Extract.Env.loadEnvironment moduleName
  match compileEnvironment env moduleName entry with
  | .ok module_ => pure module_
  | .error error => throw (IO.userError error)

end LeanExe.Extract.Arithmetic
