import LeanExe.IR.Core

namespace LeanExe.IR

/-- Calls at `module.funcs.size` and `module.funcs.size + 1` target read and write.
These are external runtime functions, not pure IR definitions. -/
structure ByteIOProgram where
  module : Module
  entryIndex : Nat

end LeanExe.IR
