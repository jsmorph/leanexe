import Project.Compiler.ScalarExecution
import LeanExe.Wasm.Binary

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition (State)

/-- The actual scalar function ABI: incoming parameters, zero-initialized
declared locals, and the production scratch allocation. -/
def functionState (func : LeanExe.IR.Func) (args : List UInt64) : State :=
  { params := args.map Wasm.Value.i64
    locals := List.replicate
      (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func) (.i64 0) }

end Project.Compiler.ScalarLowering
