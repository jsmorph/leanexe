import Project.Compiler.RuntimeValidation
import Project.Compiler.KernelReduction

namespace Project.Compiler.ArithmeticModule

open Wasm.Binary

/-- The actual fixed retain body validates in every emitted arithmetic module. -/
theorem retain_valid (func : LeanExe.IR.Func) (entry : String) (user : Code) :
    Validator.validateFunction (rawModule func entry user) (typeValues func)
      3 { params := [.i64], results := [.i64] } RuntimeEncoding.retainCode = .ok () := by
  kernel_rfl

#print axioms retain_valid

end Project.Compiler.ArithmeticModule
