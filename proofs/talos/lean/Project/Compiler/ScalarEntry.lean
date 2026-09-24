import Project.Compiler.ScalarFunction
import LeanExe.Extract.ScalarEntryCorrectness

namespace Project.Compiler.ScalarLowering

open LeanExe.Extract.Core
open Project.ProofKit.ScalarTransition (State)

/-- The normal compiler entry point succeeds on every independently supported
arithmetic declaration. Its complete emitted function body terminates with the
original source result for every input. The endpoint is interpreted structured
instructions; the module-byte/decoder boundary is deliberately not claimed. -/
theorem compileEnvironment_instructions
    {env : Lean.Environment} {moduleName entry : Lean.Name}
    {info : Lean.ConstantInfo} {source : Lean.Expr}
    (lookup : env.find? entry = some info) (body : info.value? = some source)
    (safe : info.isUnsafe = false) (total : info.isPartial = false)
    (exportable : reservedExportNames.contains (shortExportName entry) = false)
    (supported : LeanExe.Source.Scalar.DeclarationSupported info.type source) :
    ∃ func : LeanExe.IR.Func,
      compileEnvironment env moduleName entry = .ok { funcs := #[func] } ∧
      ∀ (args : List UInt64), args.length = func.params →
        ∀ (m : Wasm.Module) (host : Wasm.HostEnv α) (store : Wasm.Store α),
          ∃ (value : UInt64) (code : Wasm.Program) (next : State),
            LeanExe.Source.Scalar.Apply source [] args value ∧
            program (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs 4 func) = some code ∧
            Wasm.wp m code
              (fun outcome => outcome = .Fallthrough store (next.toLocals [.i64 value]))
              store ((functionState func args).toLocals []) host := by
  obtain ⟨func, extracted⟩ := extractScalarFunc_accepts supported entry (some (shortExportName entry))
  refine ⟨func, ?_, fun args len m host store => extracted_function_execution extracted args len 4 m host store⟩
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

end Project.Compiler.ScalarLowering
