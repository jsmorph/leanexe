import Project.Compiler.RuntimeValidation
import Project.Compiler.KernelReduction

namespace Project.Compiler.ArithmeticModule

open Wasm.Binary

/-- The actual fixed allocator body validates in every emitted arithmetic module. -/
theorem alloc_valid (func : LeanExe.IR.Func) (entry : String) (user : Code) :
    Validator.validateFunction (rawModule func entry user) (typeValues func)
      1 { params := [.i64], results := [.i64] } RuntimeEncoding.allocCode = .ok () := by
  kernel_rfl

#print axioms alloc_valid

end Project.Compiler.ArithmeticModule
