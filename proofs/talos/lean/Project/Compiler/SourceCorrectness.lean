import Project.Compiler.ModuleValidation
import Project.Compiler.SourceInvocation
import LeanExe.Extract.ArithmeticCorrectness

namespace Project.Compiler.ArithmeticModule

open LeanExe.Extract.Core
open Wasm.Binary

/-- Meaning of correctness for one original declaration and its emitted file:
complete decoding, validation, requested export, and terminating source-equal
invocation for every argument list, host environment, and store. -/
def Correct (α : Type) (source : Lean.Expr) (entry : String) (arity : Nat)
    (bytes : ByteArray) : Prop :=
  ∃ raw, Wasm.Binary.decode bytes = .ok raw ∧
    Validator.validateRaw raw = .ok () ∧
    (Translation.module raw).findExport entry = some 0 ∧
    ∀ (args : List UInt64), args.length = arity →
      ∀ (host : Wasm.HostEnv α) (store : Wasm.Store α),
        ∃ value : UInt64, LeanExe.Source.Scalar.Apply source [] args value ∧
          ∃ N, ∀ fuel ≥ N,
            Wasm.run fuel (Translation.module raw) 0 store
              (args.map Wasm.Value.i64).reverse host = .Success [.i64 value] store

/-- Meaning of correctness for one original declaration and its emitted file:
complete decoding, validation, requested export, and terminating source-equal
invocation for every argument list, host environment, and store. -/
def EnvironmentCorrect (α : Type) (env : Lean.Environment) (source : Lean.Expr) (entry : String) (arity : Nat)
    (bytes : ByteArray) : Prop :=
  ∃ raw, Wasm.Binary.decode bytes = .ok raw ∧
    Validator.validateRaw raw = .ok () ∧
    (Translation.module raw).findExport entry = some 0 ∧
    ∀ (args : List UInt64), args.length = arity →
      ∀ (host : Wasm.HostEnv α) (store : Wasm.Store α),
        ∃ value : UInt64, LeanExe.Source.Scalar.StepMatcher.EnvironmentApply env source [] args value ∧
          ∃ N, ∀ fuel ≥ N,
            Wasm.run fuel (Translation.module raw) 0 store
              (args.map Wasm.Value.i64).reverse host = .Success [.i64 value] store

theorem extracted_correct
    {name : Lean.Name} {entry : String} {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name (some entry) type source = some func)
    (available : entry ∉ reservedExportNames)
    (fits : LeanExe.Wasm.ArithmeticBounds.Fits func entry) :
    Correct α source entry func.params
      (LeanExe.Wasm.Binary.CoreWasm.moduleBytes { funcs := #[func] }) := by
  rcases fits with ⟨params, resultsBound, nameBound, localBound, bodyBound, typesBound, exportsBound, codeBound⟩
  have bounds : Bounds func entry :=
    ⟨params, resultsBound, nameBound, typesBound, exportsBound, codeBound⟩
  obtain ⟨user, declared, parsed, decoded, correct⟩ :=
    extracted_module_bytes (α := α) compiled bounds localBound bodyBound
  refine ⟨rawModule func entry user, decoded,
    extracted_module_valid compiled available localBound bodyBound user parsed,
    lookup_export func entry user, ?_⟩
  have results : func.results.length = 1 := by
    rw [(extractScalarFunc_properties compiled).2.2]
    rfl
  have localCount : func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func < 2 ^ 32 := by
    omega
  intro args len host store
  obtain ⟨value, next, applied, executed⟩ := correct args len
    (Translation.module (rawModule func entry user)) host store
  exact ⟨value, applied, run_user func entry user args len results declared localCount host store value next executed⟩

/-- Checked environment expansion preserves the complete source-to-file result. -/
theorem environment_extracted_correct
    {env : Lean.Environment} {name : Lean.Name} {entry : String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarEnvironmentFunc env name (some entry) type source = some func)
    (available : entry ∉ reservedExportNames)
    (fits : LeanExe.Wasm.ArithmeticBounds.Fits func entry) :
    EnvironmentCorrect α env source entry func.params
      (LeanExe.Wasm.Binary.CoreWasm.moduleBytes { funcs := #[func] }) := by
  obtain ⟨target, expanded, extracted⟩ := extractScalarEnvironmentFunc_cases compiled
  obtain ⟨raw, decoded, valid, exported, correct⟩ := extracted_correct (α := α) extracted available fits
  refine ⟨raw, decoded, valid, exported, ?_⟩
  intro args length host store
  obtain ⟨value, applied, executed⟩ := correct args length host store
  exact ⟨value, .expanded expanded applied, executed⟩

/-- General source-to-file compiler correctness and acceptance. The source
contract is independent syntax; the only output-side premises are numeric
format limits. No semantic/correspondence certificate is required per program. -/
theorem compileEnvironment_correct
    {env : Lean.Environment} {moduleName entry : Lean.Name}
    {info : Lean.ConstantInfo} {source : Lean.Expr}
    (lookup : env.find? entry = some info) (body : info.value? = some source)
    (safe : info.isUnsafe = false) (total : info.isPartial = false)
    (exportable : reservedExportNames.contains (shortExportName entry) = false)
    (supported : LeanExe.Source.Scalar.DeclarationSupported info.type source)
    (limits : ∀ func, extractScalarFunc entry (some (shortExportName entry)) info.type source = some func →
      LeanExe.Wasm.ArithmeticBounds.Fits func (shortExportName entry)) :
    ∃ func,
      LeanExe.Extract.Core.compileEnvironment env moduleName entry = .ok { funcs := #[func] } ∧
      LeanExe.Extract.Arithmetic.compileEnvironment env moduleName entry = .ok { funcs := #[func] } ∧
      Correct α source (shortExportName entry) func.params
        (LeanExe.Wasm.Binary.CoreWasm.moduleBytes { funcs := #[func] }) := by
  obtain ⟨func, admitted, extracted⟩ := LeanExe.Extract.Arithmetic.compileEnvironment_accepts
    (moduleName := moduleName) lookup body safe total exportable supported limits
  exact ⟨func, compileEnvironment_of_scalar_extraction lookup body safe total exportable extracted,
    admitted, extracted_correct extracted (by simpa using exportable) (limits func extracted)⟩

/-- General source-to-file compiler correctness and acceptance. The source
contract is independent syntax; the only output-side premises are numeric
format limits. No semantic/correspondence certificate is required per program. -/
theorem compileEnvironment_environment_correct
    {env : Lean.Environment} {moduleName entry : Lean.Name}
    {info : Lean.ConstantInfo} {source : Lean.Expr}
    (lookup : env.find? entry = some info) (body : info.value? = some source)
    (safe : info.isUnsafe = false) (total : info.isPartial = false)
    (exportable : reservedExportNames.contains (shortExportName entry) = false)
    (supported : LeanExe.Source.Scalar.StepMatcher.EnvironmentSupported env info.type source)
    (limits : ∀ func, extractScalarEnvironmentFunc env entry (some (shortExportName entry)) info.type source = some func →
      LeanExe.Wasm.ArithmeticBounds.Fits func (shortExportName entry)) :
    ∃ func,
      LeanExe.Extract.Core.compileEnvironment env moduleName entry = .ok { funcs := #[func] } ∧
      LeanExe.Extract.Arithmetic.compileEnvironment env moduleName entry = .ok { funcs := #[func] } ∧
      EnvironmentCorrect α env source (shortExportName entry) func.params
        (LeanExe.Wasm.Binary.CoreWasm.moduleBytes { funcs := #[func] }) := by
  obtain ⟨func, admitted, extracted⟩ := LeanExe.Extract.Arithmetic.compileEnvironment_environment_accepts
    (moduleName := moduleName) lookup body safe total exportable supported limits
  exact ⟨func, compileEnvironment_of_scalar_environment_extraction lookup body safe total exportable extracted,
    admitted, environment_extracted_correct extracted (by simpa using exportable) (limits func extracted)⟩

/-- Every file accepted by the shipped arithmetic mode has the source-to-file
correctness property, without any semantic premise supplied by its caller. -/
theorem compileEnvironment_sound
    {env : Lean.Environment} {moduleName entry : Lean.Name} {module_ : LeanExe.IR.Module}
    (compiled : LeanExe.Extract.Arithmetic.compileEnvironment env moduleName entry = .ok module_) :
    ∃ info source func,
      env.find? entry = some info ∧ info.value? = some source ∧
      module_ = { funcs := #[func] } ∧
      EnvironmentCorrect α env source (shortExportName entry) func.params
        (LeanExe.Wasm.Binary.CoreWasm.moduleBytes module_) := by
  obtain ⟨info, source, func, lookup, body, _, _, exportable, extracted, fits, same⟩ :=
    LeanExe.Extract.Arithmetic.compileEnvironment_success compiled
  refine ⟨info, source, func, lookup, body, same, ?_⟩
  rw [same]
  exact environment_extracted_correct extracted (by simpa using exportable) fits

end Project.Compiler.ArithmeticModule
