import Project.Compiler.ArithmeticFunctionBytes
import Project.Compiler.FunctionParsing

namespace Project.Compiler.ArithmeticEncoding

open LeanExe.Extract.Core
open LeanExe.Wasm.ScalarDescriptor

/-- General preservation from original arithmetic source to the exact production
function-body bytes, including declared locals and the body-size prefix.
The enclosing module and exported invocation are not asserted here. -/
theorem extracted_function_body_bytes
    {name : Lean.Name} {exportName : Option String} {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name exportName type source = some func)
    (releaseIndex : Nat)
    (localBound : func.locals + LeanExe.Wasm.Binary.CoreWasm.funcScratch func < 2 ^ 32)
    (bodyBound : (LeanExe.Wasm.Binary.CoreWasm.localDecls func ++
      LeanExe.Wasm.Binary.CoreWasm.encodeInstrs
        (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex func) ++ [11]).length < 2 ^ 32)
    (args : List UInt64) (len : args.length = func.params)
    (m : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α) :
    ∃ (value : UInt64) (raw : List Wasm.Binary.Instr) (next : Project.ProofKit.ScalarTransition.State),
      LeanExe.Source.Scalar.Apply source [] args value ∧
      Parsing.Parses Wasm.Binary.code (LeanExe.Wasm.Binary.CoreWasm.emitFuncBody releaseIndex func)
        { locals := Parsing.i64Locals (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func)
          body := raw } ∧
      Wasm.wp m (Wasm.Binary.Instr.listToTalos raw)
        (fun outcome => outcome = .Fallthrough store (next.toLocals [.i64 value]))
        store ((ScalarLowering.functionState func args).toLocals []) env := by
  simp only [extractScalarFunc, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
  obtain ⟨arity, ha, body, hb, ir, hi, rfl⟩ := compiled
  have hlen : args.length = arity := len
  subst arity
  have supported := extractScalarExpr_supported hi
  obtain ⟨value, semantics⟩ := supported.evaluates args.reverse (by simp)
  have applied := LeanExe.Source.Scalar.apply_of_collectLambdas args [] hb (by simpa using semantics)
  have irEval := extractScalarExpr_correct semantics hi (scalarArgumentLocals args [0])
  obtain ⟨descriptor, recognized, arithmetic⟩ := extractScalarExpr_arithmetic hi
  have scratch := scalarFunc_scratch args.length name exportName recognized
  have room : args.length + 1 + descriptor.scratchWidth ≤ 2 ^ 32 := by
    rw [scratch] at localBound
    change args.length + 1 + descriptor.scratchWidth < 2 ^ 32 at localBound
    omega
  have reads : ∀ index ∈ descriptor.reads, index < 2 ^ 32 := by
    intro index member
    have h := extractScalarExpr_reads hi recognized (count := args.length)
      (by intro slot present; simpa using present) index member
    omega
  obtain ⟨raw, encoded⟩ := scalar_function_encodable name exportName args.length
    releaseIndex recognized arithmetic reads room
  obtain ⟨code, next, lowered, executed⟩ := ScalarLowering.scalar_function_execution args
    name exportName releaseIndex recognized irEval m env store
  obtain ⟨translated, ht, related⟩ := encoded.translation
  have same : translated = code := Option.some.inj (ht.symm.trans lowered)
  subst translated
  refine ⟨value, raw, next, applied, ?_, (related.wp_iff m store _ env _).mpr executed⟩
  apply Parsing.function_body releaseIndex encoded
  · simp [scalarFunc]
  · dsimp only [scalarFunc] at localBound ⊢
    omega
  · exact bodyBound

end Project.Compiler.ArithmeticEncoding
