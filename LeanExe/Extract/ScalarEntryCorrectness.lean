import LeanExe.Extract.Core

namespace LeanExe.Extract.Core

theorem compileEnvironment_scalar {env : Lean.Environment} {moduleName entry : Lean.Name}
    {compiled : CompiledModule} (h : extractScalarEntry? true env moduleName entry = some compiled) :
    compileEnvironment env moduleName entry = .ok compiled.module := by
  simp [compileEnvironment, compileEnvironmentWithEntryMode,
    compileEnvironmentWithEntryModeDetailed, h]

/-- Successful scalar extraction reaches the unchanged normal compiler entry. -/
theorem compileEnvironment_of_scalar_extraction
    {env : Lean.Environment} {moduleName entry : Lean.Name}
    {info : Lean.ConstantInfo} {source : Lean.Expr} {func : LeanExe.IR.Func}
    (lookup : env.find? entry = some info) (body : info.value? = some source)
    (safe : info.isUnsafe = false) (total : info.isPartial = false)
    (exportable : reservedExportNames.contains (shortExportName entry) = false)
    (extracted : extractScalarFunc entry (some (shortExportName entry)) info.type source = some func) :
    compileEnvironment env moduleName entry = .ok { funcs := #[func] } := by
  have available : shortExportName entry ∉ reservedExportNames := by simpa using exportable
  have hentry : extractScalarEntry? true env moduleName entry = some {
      ctx := {
        env := env
        root := moduleName.getRoot
        names := #[entry]
        synthetics := #[]
        freshResultOwnerOffsets := #[[]]
        inlineStack := [] }
      module := { funcs := #[func] }
      releaseJudgments := #[] } := by
    simp [extractScalarEntry?, lookup, body, safe, total, available, extracted]
  exact compileEnvironment_scalar hentry

/-- A general theorem about the actual production compiler entry point and
original source declaration. Its endpoint is the existing IR, not WASM bytes.
All supported declarations and all argument lists of the declared arity are
quantified here; no individual correspondence certificate is assumed. -/
theorem compileEnvironment_scalar_total_correct
    {env : Lean.Environment} {moduleName entry : Lean.Name}
    {info : Lean.ConstantInfo} {source : Lean.Expr}
    (lookup : env.find? entry = some info) (body : info.value? = some source)
    (safe : info.isUnsafe = false) (total : info.isPartial = false)
    (exportable : reservedExportNames.contains (shortExportName entry) = false)
    (supported : LeanExe.Source.Scalar.DeclarationSupported info.type source) :
    ∃ func : LeanExe.IR.Func,
      compileEnvironment env moduleName entry = .ok { funcs := #[func] } ∧
      ∀ args : List UInt64, args.length = func.params →
        ∃ value, LeanExe.Source.Scalar.Apply source [] args value ∧ func.ScalarEval args value := by
  obtain ⟨func, extracted⟩ := extractScalarFunc_accepts supported entry (some (shortExportName entry))
  refine ⟨func, ?_, fun args len => extractScalarFunc_correct extracted args len⟩
  have available : shortExportName entry ∉ reservedExportNames := by simpa using exportable
  have hentry : extractScalarEntry? true env moduleName entry = some {
      ctx := {
        env := env
        root := moduleName.getRoot
        names := #[entry]
        synthetics := #[]
        freshResultOwnerOffsets := #[[]]
        inlineStack := [] }
      module := { funcs := #[func] }
      releaseJudgments := #[] } := by
    simp [extractScalarEntry?, lookup, body, safe, total, available, extracted]
  exact compileEnvironment_scalar hentry

end LeanExe.Extract.Core
