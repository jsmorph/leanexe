import Project.Compiler.RuntimeValidation
import Project.Compiler.KernelReduction

namespace Project.Compiler.ArithmeticModule

open Wasm.Binary

/-- The actual fixed release body validates in every emitted arithmetic module. -/
theorem release_valid (func : LeanExe.IR.Func) (entry : String) (user : Code) :
    Validator.validateFunction (rawModule func entry user) (typeValues func)
      4 { params := [.i64], results := [] } RuntimeEncoding.releaseCode = .ok () := by
  kernel_rfl

#print axioms release_valid

end Project.Compiler.ArithmeticModule
