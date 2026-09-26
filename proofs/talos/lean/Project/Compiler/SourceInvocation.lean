import Project.Compiler.ModuleInvocation

namespace Project.Compiler.ArithmeticModule

open LeanExe.Extract.Core

/-- Exact emitted module bytes, the requested export, and total invocation
correctness for every source argument list. Module validation is not asserted
by this theorem and is the next separate proof obligation. -/
theorem extracted_module_invocation
    {name : Lean.Name} {entry : String} {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name (some entry) type source = some func)
    (bounds : Bounds func entry)
    (localBound : func.locals + LeanExe.Wasm.Binary.CoreWasm.funcScratch func < 2 ^ 32)
    (bodyBound : (LeanExe.Wasm.Binary.CoreWasm.localDecls func ++
      LeanExe.Wasm.Binary.CoreWasm.encodeInstrs
        (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs 4 func) ++ [11]).length < 2 ^ 32) :
    ∃ user : Wasm.Binary.Code,
      Wasm.Binary.decode (LeanExe.Wasm.Binary.CoreWasm.moduleBytes { funcs := #[func] }) =
        .ok (rawModule func entry user) ∧
      (Wasm.Binary.Translation.module (rawModule func entry user)).findExport entry = some 0 ∧
      ∀ (args : List UInt64), args.length = func.params →
        ∀ (host : Wasm.HostEnv α) (store : Wasm.Store α),
          ∃ value : UInt64,
            LeanExe.Source.Scalar.Apply source [] args value ∧
            ∃ N, ∀ fuel ≥ N,
              Wasm.run fuel (Wasm.Binary.Translation.module (rawModule func entry user))
                0 store (args.map Wasm.Value.i64).reverse host = .Success [.i64 value] store := by
  obtain ⟨user, declared, _, decoded, correct⟩ :=
    extracted_module_bytes (α := α) compiled bounds localBound bodyBound
  have results : func.results.length = 1 := by
    rw [(extractScalarFunc_properties compiled).2.2]
    rfl
  have localCount : func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func < 2 ^ 32 := by
    omega
  refine ⟨user, decoded, lookup_export func entry user, ?_⟩
  intro args len host store
  obtain ⟨value, next, applied, executed⟩ := correct args len
    (Wasm.Binary.Translation.module (rawModule func entry user)) host store
  exact ⟨value, applied, run_user func entry user args len results declared localCount host store value next executed⟩

end Project.Compiler.ArithmeticModule
