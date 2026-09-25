import Project.Compiler.MetadataValidation
import Project.Compiler.SourceFunctionValidation
import Project.Compiler.RuntimeAllocValidation
import Project.Compiler.RuntimeRetainValidation
import Project.Compiler.RuntimeReleaseValidation
import Project.Artifact.Binary.ValidationParts

namespace Project.Compiler.ArithmeticModule

open Wasm.Binary

/-- Every component of the actual emitted arithmetic module passes the
existing whole-module validator, including all four runtime functions. -/
theorem extracted_module_valid
    {name : Lean.Name} {entry : String} {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : LeanExe.Extract.Core.extractScalarFunc name (some entry) type source = some func)
    (available : entry ∉ LeanExe.Extract.Core.reservedExportNames)
    (localBound : func.locals + LeanExe.Wasm.Binary.CoreWasm.funcScratch func < 2 ^ 32)
    (bodyBound : (LeanExe.Wasm.Binary.CoreWasm.localDecls func ++
      LeanExe.Wasm.Binary.CoreWasm.encodeInstrs
        (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs 4 func) ++ [11]).length < 2 ^ 32)
    (user : Code)
    (parsed : Parsing.Parses code (LeanExe.Wasm.Binary.CoreWasm.emitFuncBody 4 func) user) :
    Validator.validateRaw (rawModule func entry user) = .ok () := by
  apply validateRaw_eq_of_parts (functions := typeValues func)
    (sections_valid func entry user) rfl (limits_valid func entry user)
    (globals_valid func entry user) (exports_valid func entry user available)
    (types_resolved func entry user)
  unfold Validator.validateFunctions
  change Validator.validateFunctionPairs (rawModule func entry user) (typeValues func) 0
    (typeValues func) (codeValues user) = .ok ()
  apply validateFunctionPairs_eq_cons
    (ArithmeticValidation.extracted_function_valid compiled localBound bodyBound user parsed)
  apply validateFunctionPairs_eq_cons (alloc_valid func entry user)
  apply validateFunctionPairs_eq_cons (reset_valid func entry user)
  apply validateFunctionPairs_eq_cons (retain_valid func entry user)
  apply validateFunctionPairs_eq_cons (release_valid func entry user)
  rfl

end Project.Compiler.ArithmeticModule
