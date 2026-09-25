import LeanExe.Extract.Core

/-! The actual compiler must reject every runtime export-name collision, while
allowing ordinary exports and internal functions with the same short names. -/
namespace RuntimeExportNames
def memory (x : UInt64) : UInt64 := x + 1
def alloc (x : UInt64) : UInt64 := x + 1
def reset (x : UInt64) : UInt64 := x + 1
def retain (x : UInt64) : UInt64 := x + 1
def release (x : UInt64) : UInt64 := x + 1
def free (x : UInt64) : UInt64 := x + 1
def allocCount (x : UInt64) : UInt64 := x + 1
def retainCount (x : UInt64) : UInt64 := x + 1
def releaseCount (x : UInt64) : UInt64 := x + 1
def freeCount (x : UInt64) : UInt64 := x + 1
def arithmetic (x : UInt64) : UInt64 := x + 1
end RuntimeExportNames

run_elab do
  let env ← Lean.getEnv
  let names : List Lean.Name := [`RuntimeExportNames.memory, `RuntimeExportNames.alloc, `RuntimeExportNames.reset, `RuntimeExportNames.retain, `RuntimeExportNames.release, `RuntimeExportNames.free, `RuntimeExportNames.allocCount, `RuntimeExportNames.retainCount, `RuntimeExportNames.releaseCount, `RuntimeExportNames.freeCount]
  for name in names do
    match LeanExe.Extract.Core.compileEnvironment env `RuntimeExportNames name with
    | .ok _ => throwError "accepted a colliding runtime export: {name}"
    | .error message =>
      if (message.splitOn "entry export name is reserved by the runtime ABI:").length == 1 then
        throwError "unexpected rejection for {name}: {message}"
    match LeanExe.Extract.Core.compileEnvironmentWithEntryMode false env `RuntimeExportNames name with
    | .error message => throwError "internal function unexpectedly rejected: {name}: {message}"
    | .ok module_ =>
      let some func := module_.funcs[0]? | throwError "missing internal function: {name}"
      unless func.exportName.isNone do
        throwError "internal function unexpectedly exported: {name}"
  match LeanExe.Extract.Core.compileEnvironment env `RuntimeExportNames `RuntimeExportNames.arithmetic with
  | .error message => throwError "ordinary arithmetic export rejected: {message}"
  | .ok module_ =>
    let some func := module_.funcs[0]? | throwError "missing arithmetic function"
    unless func.exportName == some "arithmetic" do
      throwError "ordinary arithmetic export name changed"
