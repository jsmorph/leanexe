import Project.Compiler.SourceModuleBytes

namespace Project.Compiler.ArithmeticModule

open Project.Compiler.Parsing
open Wasm.Binary

def userFunction (func : LeanExe.IR.Func) (user : Code) : Wasm.Function :=
  { params := List.replicate func.params .i64
    locals := Translation.expandLocals user.locals
    body := Instr.listToTalos user.body
    results := List.replicate func.results.length .i64
    typeIdx := some 0 }

theorem lookup_user (func : LeanExe.IR.Func) (entry : String) (user : Code) :
    (Translation.module (rawModule func entry user)).funcs[0]? = some (userFunction func user) := by
  change some (Translation.functionToTalos (rawModule func entry user) 0 user) = _
  simp [Translation.functionToTalos, rawModule, typeValues, userFunction, ValType.toTalos]

theorem lookup_export (func : LeanExe.IR.Func) (entry : String) (user : Code) :
    (Translation.module (rawModule func entry user)).findExport entry = some 0 := by
  simp [Wasm.Module.findExport, Translation.module, Translation.functionExports,
    rawModule, exportValues, exportValue, ExportKind.desc]

theorem initial_locals (func : LeanExe.IR.Func) (user : Code) (args : List UInt64)
    (declared : user.locals = i64Locals
      (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func))
    (bound : func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func < 2 ^ 32) :
    (userFunction func user).toLocals (args.map Wasm.Value.i64) =
      (ScalarLowering.functionState func args).toLocals [] := by
  simp [userFunction, Wasm.Function.toLocals, declared, i64Locals, Translation.expandLocals,
    UInt32.toNat_ofNat_of_lt' bound, ValType.toTalos, Wasm.ValueType.zero,
    ScalarLowering.functionState, Project.ProofKit.ScalarTransition.State.toLocals]
  exact bound

/-- The actual exported-call ABI: source-order arguments are reversed into the
interpreter's operand-stack order, restored as locals, and one i64 is returned. -/
theorem run_user (func : LeanExe.IR.Func) (entry : String) (user : Code)
    (args : List UInt64) (len : args.length = func.params)
    (results : func.results.length = 1)
    (declared : user.locals = i64Locals
      (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func))
    (bound : func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func < 2 ^ 32)
    (host : Wasm.HostEnv α) (store : Wasm.Store α) (value : UInt64)
    (next : Project.ProofKit.ScalarTransition.State)
    (executed : Wasm.wp (Translation.module (rawModule func entry user))
      (Instr.listToTalos user.body)
      (fun outcome => outcome = .Fallthrough store (next.toLocals [.i64 value]))
      store ((ScalarLowering.functionState func args).toLocals []) host) :
    ∃ N, ∀ fuel ≥ N,
      Wasm.run fuel (Translation.module (rawModule func entry user)) 0 store
        (args.map Wasm.Value.i64).reverse host = .Success [.i64 value] store := by
  unfold Wasm.wp at executed
  obtain ⟨N, hN⟩ := executed
  refine ⟨N, ?_⟩
  intro fuel enough
  have done := hN fuel enough
  have frame := initial_locals func user args declared bound
  have count : (args.map Wasm.Value.i64).reverse.length = func.params := by simp [len]
  have taken : (args.map Wasm.Value.i64).reverse.take func.params =
      (args.map Wasm.Value.i64).reverse := by rw [← count, List.take_length]
  have dropped : (args.map Wasm.Value.i64).reverse.drop func.params = [] := by
    rw [← count, List.drop_length]
  have noImports : (Translation.module (rawModule func entry user)).imports = [] := rfl
  rw [Wasm.run]
  simp only [noImports, List.getElem?_nil, List.length_nil, Nat.sub_zero,
    lookup_user, Wasm.Function.numParams, userFunction, List.length_replicate,
    taken, List.reverse_reverse, dropped]
  dsimp only [userFunction] at frame
  rw [frame, done]
  simp [results]

end Project.Compiler.ArithmeticModule
