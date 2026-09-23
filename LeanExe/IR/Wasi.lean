import LeanExe.IR.Core

namespace LeanExe.IR

/-- External calls follow the order in `LeanExe.Wasi.primitives`, after `module.funcs`. -/
structure WasiProgram where
  module : Module
  entryIndex : Nat

end LeanExe.IR
