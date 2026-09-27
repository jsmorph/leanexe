import Project.Compiler.SourceCorrectness

namespace Project.Compiler.ArithmeticModule
open LeanExe.Extract.Core LeanExe.Wasm.ScalarDescriptor
open Project.Compiler.Parsing Project.Compiler.ArithmeticEncoding

/-- A scalar controller's proved IR result reaches the actual decoded module's
export. This lets application contracts name a specific native Lean result. -/
theorem scalar_result (args : List UInt64) (name : Lean.Name) (entry : String)
    {ir : LeanExe.IR.Expr} {descriptor : Expr} {value : UInt64}
    (recognized : Expr.ofIR ir = some descriptor) (arithmetic : descriptor.Arithmetic)
    (reads : ∀ index ∈ descriptor.reads, index < 2 ^ 32)
    (evaluated : ir.ScalarEval (args ++ [0]) value (args ++ [0]))
    (fits : LeanExe.Wasm.ArithmeticBounds.Fits
      (scalarFunc name (some entry) args.length ir) entry)
    (host : Wasm.HostEnv α) (store : Wasm.Store α) :
    ∃ raw, Wasm.Binary.decode (LeanExe.Wasm.Binary.CoreWasm.moduleBytes
      { funcs := #[scalarFunc name (some entry) args.length ir] }) = .ok raw ∧
      (Wasm.Binary.Translation.module raw).findExport entry = some 0 ∧
      ∃ N, ∀ fuel ≥ N, Wasm.run fuel (Wasm.Binary.Translation.module raw) 0 store
        (args.map Wasm.Value.i64).reverse host = .Success [.i64 value] store := by
  let func := scalarFunc name (some entry) args.length ir
  rcases fits with ⟨params, resultsBound, nameBound, localBound, bodyBound,
    typesBound, exportsBound, codeBound⟩
  have bounds : Bounds func entry :=
    ⟨params, resultsBound, nameBound, typesBound, exportsBound, codeBound⟩
  have scratch := scalarFunc_scratch args.length name (some entry) recognized
  have room : args.length + 1 + descriptor.scratchWidth ≤ 2 ^ 32 := by
    rw [scratch] at localBound
    change args.length + 1 + descriptor.scratchWidth < 2 ^ 32 at localBound
    omega
  obtain ⟨raw, encoded⟩ := scalar_function_encodable name (some entry) args.length
    4 recognized arithmetic reads room
  have small : func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func < 2^32 := by
    dsimp [func, scalarFunc] at localBound ⊢
    omega
  have parsed := function_body 4 encoded (by simp [scalarFunc]) small bodyBound
  let user : Wasm.Binary.Code :=
    { locals := i64Locals (func.locals-func.params+LeanExe.Wasm.Binary.CoreWasm.funcScratch func)
      body := raw }
  refine ⟨rawModule func entry user,
    decode_actual_module func entry user rfl parsed bounds, lookup_export func entry user, ?_⟩
  obtain ⟨code, next, lowered, executed⟩ := ScalarLowering.scalar_function_execution args
    name (some entry) 4 recognized evaluated
    (Wasm.Binary.Translation.module (rawModule func entry user)) host store
  obtain ⟨translated, ht, related⟩ := encoded.translation
  have same : translated = code := Option.some.inj (ht.symm.trans lowered)
  subst translated
  exact run_user func entry user args rfl rfl rfl small host store value next
    ((related.wp_iff _ store _ host _).mpr executed)

end Project.Compiler.ArithmeticModule
