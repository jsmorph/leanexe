import Project.Compiler.ArithmeticModuleBytes
import Project.Artifact.Binary.Validate

namespace Project.Compiler.ArithmeticModule

open Wasm.Binary

/-- Validation of the fixed reset body in the actual surrounding module. -/
theorem reset_valid (func : LeanExe.IR.Func) (entry : String) (user : Code) :
    Validator.validateFunction (rawModule func entry user) (typeValues func)
      2 { params := [], results := [] } RuntimeEncoding.resetCode = .ok () := by
  rfl

end Project.Compiler.ArithmeticModule
