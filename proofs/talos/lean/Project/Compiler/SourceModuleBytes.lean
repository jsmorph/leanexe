import Project.Compiler.ArithmeticModuleBytes
import Project.Compiler.SourceFunctionBytes

namespace Project.Compiler.Parsing

theorem Parses.unique {parser : Wasm.Binary.Parser α} {bytes : List UInt8} {a b : α}
    (left : Parses parser bytes a) (right : Parses parser bytes b) : a = b := by
  have l := left [] [] bytes.length (by simp) (by simp)
  have r := right [] [] bytes.length (by simp) (by simp)
  exact congrArg Prod.fst (Except.ok.inj (l.symm.trans r))

end Project.Compiler.Parsing

namespace Project.Compiler.ArithmeticModule

open LeanExe.Extract.Core
open Project.Compiler.Parsing

theorem extracted_export {name : Lean.Name} {entry : String} {type source : Lean.Expr}
    {func : LeanExe.IR.Func} (compiled : extractScalarFunc name (some entry) type source = some func) :
    func.exportName = some entry := by
  simp only [extractScalarFunc, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
  obtain ⟨arity, _, body, _, ir, _, rfl⟩ := compiled
  rfl

/-- Original source to exact whole production module bytes, with execution of
its decoded user body for every input and every surrounding module/store.
Validation and exported invocation are deliberately separate remaining goals. -/
theorem extracted_module_bytes
    {name : Lean.Name} {entry : String} {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name (some entry) type source = some func)
    (bounds : Bounds func entry)
    (localBound : func.locals + LeanExe.Wasm.Binary.CoreWasm.funcScratch func < 2 ^ 32)
    (bodyBound : (LeanExe.Wasm.Binary.CoreWasm.localDecls func ++
      LeanExe.Wasm.Binary.CoreWasm.encodeInstrs
        (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs 4 func) ++ [11]).length < 2 ^ 32) :
    ∃ user : Wasm.Binary.Code,
      user.locals = i64Locals (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func) ∧
      Parses Wasm.Binary.code (LeanExe.Wasm.Binary.CoreWasm.emitFuncBody 4 func) user ∧
      Wasm.Binary.decode (LeanExe.Wasm.Binary.CoreWasm.moduleBytes { funcs := #[func] }) =
        .ok (rawModule func entry user) ∧
      ∀ (args : List UInt64), args.length = func.params →
        ∀ (m : Wasm.Module) (host : Wasm.HostEnv α) (store : Wasm.Store α),
          ∃ (value : UInt64) (next : Project.ProofKit.ScalarTransition.State),
            LeanExe.Source.Scalar.Apply source [] args value ∧
            Wasm.wp m (Wasm.Binary.Instr.listToTalos user.body)
              (fun outcome => outcome = .Fallthrough store (next.toLocals [.i64 value]))
              store ((ScalarLowering.functionState func args).toLocals []) host := by
  -- Select the unique decoding. The universal execution proof below is applied
  -- afresh to every argument list; no execution result of this witness is used.
  let witnessModule : Wasm.Module := { funcs := [] }
  obtain ⟨_, raw, _, _, parsed, _⟩ :=
    ArithmeticEncoding.extracted_function_body_bytes compiled 4 localBound bodyBound
      (List.replicate func.params 0) (by simp) witnessModule ({} : Wasm.HostEnv Unit)
      (witnessModule.initialStore (α := Unit))
  refine ⟨_, rfl, parsed, decode_actual_module func entry _ (extracted_export compiled) parsed bounds, ?_⟩
  intro args len m host store
  obtain ⟨value, raw', next, sourceValue, parsed', executed⟩ :=
    ArithmeticEncoding.extracted_function_body_bytes compiled 4 localBound bodyBound args len m host store
  have same : raw = raw' := congrArg Wasm.Binary.Code.body (parsed.unique parsed')
  subst raw'
  exact ⟨value, next, sourceValue, executed⟩

end Project.Compiler.ArithmeticModule
