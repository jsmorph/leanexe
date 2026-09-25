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
    simp only [extractScalarFunc, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨arity, _, body, _, ir, _, rfl⟩ := compiled
    rfl
  have localCount : func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func < 2 ^ 32 := by
    omega
  intro args len host store
  obtain ⟨value, next, applied, executed⟩ := correct args len
    (Translation.module (rawModule func entry user)) host store
  exact ⟨value, applied, run_user func entry user args len results declared localCount host store value next executed⟩

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

/-- Every file accepted by the shipped arithmetic mode has the source-to-file
correctness property, without any semantic premise supplied by its caller. -/
theorem compileEnvironment_sound
    {env : Lean.Environment} {moduleName entry : Lean.Name} {module_ : LeanExe.IR.Module}
    (compiled : LeanExe.Extract.Arithmetic.compileEnvironment env moduleName entry = .ok module_) :
    ∃ info source func,
      env.find? entry = some info ∧ info.value? = some source ∧
      module_ = { funcs := #[func] } ∧
      Correct α source (shortExportName entry) func.params
        (LeanExe.Wasm.Binary.CoreWasm.moduleBytes module_) := by
  obtain ⟨info, source, func, lookup, body, _, _, exportable, extracted, fits, same⟩ :=
    LeanExe.Extract.Arithmetic.compileEnvironment_success compiled
  refine ⟨info, source, func, lookup, body, same, ?_⟩
  rw [same]
  exact extracted_correct extracted (by simpa using exportable) fits

end Project.Compiler.ArithmeticModule
