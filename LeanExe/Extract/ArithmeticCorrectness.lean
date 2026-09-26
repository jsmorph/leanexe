import LeanExe.Extract.Arithmetic

namespace LeanExe.Extract.Arithmetic

open LeanExe.Extract.Core

/-- Admission checks preserve the exact existing compiler result. -/
theorem compileEnvironment_of_extracted
    {env : Lean.Environment} {moduleName entry : Lean.Name}
    {info : Lean.ConstantInfo} {source : Lean.Expr} {func : LeanExe.IR.Func}
    (lookup : env.find? entry = some info) (body : info.value? = some source)
    (safe : info.isUnsafe = false) (total : info.isPartial = false)
    (exportable : reservedExportNames.contains (shortExportName entry) = false)
    (extracted : extractScalarFunc entry (some (shortExportName entry)) info.type source = some func)
    (fits : LeanExe.Wasm.ArithmeticBounds.Fits func (shortExportName entry)) :
    compileEnvironment env moduleName entry = .ok { funcs := #[func] } := by
  have normal := compileEnvironment_of_scalar_extraction (moduleName := moduleName)
    lookup body safe total exportable extracted
  have available : shortExportName entry ∉ reservedExportNames := by simpa using exportable
  simp [compileEnvironment, lookup, body, safe, total, available, extracted, fits, normal]

/-- The independent source grammar, together with only numeric format limits,
implies that strict arithmetic compilation succeeds. -/
theorem compileEnvironment_accepts
    {env : Lean.Environment} {moduleName entry : Lean.Name}
    {info : Lean.ConstantInfo} {source : Lean.Expr}
    (lookup : env.find? entry = some info) (body : info.value? = some source)
    (safe : info.isUnsafe = false) (total : info.isPartial = false)
    (exportable : reservedExportNames.contains (shortExportName entry) = false)
    (supported : LeanExe.Source.Scalar.DeclarationSupported info.type source)
    (limits : ∀ func, extractScalarFunc entry (some (shortExportName entry)) info.type source = some func →
      LeanExe.Wasm.ArithmeticBounds.Fits func (shortExportName entry)) :
    ∃ func, compileEnvironment env moduleName entry = .ok { funcs := #[func] } ∧
      extractScalarFunc entry (some (shortExportName entry)) info.type source = some func := by
  obtain ⟨func, extracted⟩ := extractScalarFunc_accepts supported entry (some (shortExportName entry))
  exact ⟨func, compileEnvironment_of_extracted lookup body safe total exportable extracted
    (limits func extracted), extracted⟩

/-- Successful strict admission exposes the original declaration and the
numeric limits used by the general source-to-bytes proof. -/
theorem compileEnvironment_success
    {env : Lean.Environment} {moduleName entry : Lean.Name} {module_ : LeanExe.IR.Module}
    (compiled : compileEnvironment env moduleName entry = .ok module_) :
    ∃ info source func,
      env.find? entry = some info ∧ info.value? = some source ∧
      info.isUnsafe = false ∧ info.isPartial = false ∧
      reservedExportNames.contains (shortExportName entry) = false ∧
      extractScalarFunc entry (some (shortExportName entry)) info.type source = some func ∧
      LeanExe.Wasm.ArithmeticBounds.Fits func (shortExportName entry) ∧
      module_ = { funcs := #[func] } := by
  cases lookup : env.find? entry with
  | none => simp [compileEnvironment, lookup] at compiled
  | some info =>
    cases safe : info.isUnsafe <;> cases total : info.isPartial <;>
      simp only [compileEnvironment, lookup, safe, total, Bool.or_false, Bool.false_or,
        Bool.or_true, Bool.true_or, Bool.false_eq_true, if_false, if_true] at compiled
    all_goals try contradiction
    cases body : info.value? with
    | none => simp [body] at compiled
    | some source =>
      simp only [body] at compiled
      cases exportable : reservedExportNames.contains (shortExportName entry) with
      | true =>
        have present : shortExportName entry ∈ reservedExportNames := by simpa using exportable
        simp [present] at compiled
      | false =>
        simp only [exportable, Bool.false_eq_true, if_false] at compiled
        cases extracted : extractScalarFunc entry (some (shortExportName entry)) info.type source with
        | none => simp [extracted] at compiled
        | some func =>
          simp only [extracted] at compiled
          by_cases fits : LeanExe.Wasm.ArithmeticBounds.Fits func (shortExportName entry)
          · have normal := compileEnvironment_of_scalar_extraction (moduleName := moduleName)
              lookup body safe total exportable extracted
            have same : module_ = { funcs := #[func] } := by
              simpa [fits, normal, eq_comm] using compiled
            exact ⟨info, source, func, rfl, body, safe, total, rfl, extracted, fits, same⟩
          · simp [fits] at compiled

end LeanExe.Extract.Arithmetic
