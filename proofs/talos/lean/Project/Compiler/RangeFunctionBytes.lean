import Project.Compiler.RangeTyping
import Project.Compiler.RangeFunctionExecution
import Project.Compiler.ArithmeticTranslation
import Project.Compiler.FunctionParsing

namespace Project.Compiler.ArithmeticEncoding

open LeanExe.Wasm.ScalarDescriptor

/-- The complete range-function bytes parse and execute with the source value,
including local declarations and the size prefix used by the actual emitter. -/
theorem range_function_body_bytes (args : List UInt64) (name : Lean.Name)
    (exportName : Option String) (releaseIndex : Nat)
    {plan : LeanExe.Extract.Core.ScalarRangePlan} {descriptor : Range} {value : UInt64}
    (matched : descriptor.Matches plan) (arithmetic : descriptor.All Expr.Arithmetic)
    (reads : descriptor.All (fun e => ∀ index ∈ e.reads, index < args.length + 3))
    (meaning : plan.Meaning args value)
    (localBound : (plan.func name exportName args.length).locals +
      LeanExe.Wasm.Binary.CoreWasm.funcScratch (plan.func name exportName args.length) < 2 ^ 32)
    (bodyBound : (LeanExe.Wasm.Binary.CoreWasm.localDecls (plan.func name exportName args.length) ++
      LeanExe.Wasm.Binary.CoreWasm.encodeInstrs
        (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex (plan.func name exportName args.length)) ++ [11]).length < 2 ^ 32)
    (m : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α) :
    ∃ (raw : List Wasm.Binary.Instr) (next : Project.ProofKit.ScalarTransition.State),
      Parsing.Parses Wasm.Binary.code
        (LeanExe.Wasm.Binary.CoreWasm.emitFuncBody releaseIndex (plan.func name exportName args.length))
        { locals := Parsing.i64Locals (3 + descriptor.scratchWidth), body := raw } ∧
      Wasm.wp m (Wasm.Binary.Instr.listToTalos raw)
        (fun outcome => outcome = .Fallthrough store (next.toLocals [.i64 value]))
        store ((ScalarLowering.functionState (plan.func name exportName args.length) args).toLocals []) env := by
  have scratch := Range.func_scratch matched args.length name exportName
  have format : args.length + 3 + descriptor.scratchWidth < 2 ^ 32 := by
    rw [scratch] at localBound
    exact localBound
  obtain ⟨raw, encoded, _⟩ := ArithmeticValidation.range_function_sequence matched arithmetic
    args.length releaseIndex name exportName reads format
  obtain ⟨code, next, lowered, executed⟩ := ScalarLowering.range_function_execution
    args name exportName releaseIndex matched meaning m env store
  obtain ⟨translated, ht, related⟩ := encoded.translation
  have same : translated = code := Option.some.inj (ht.symm.trans lowered)
  subst translated
  refine ⟨raw, next, ?_, (related.wp_iff m store _ env _).mpr executed⟩
  have parsed := Parsing.function_body releaseIndex encoded
    (by simp [LeanExe.Extract.Core.ScalarRangePlan.func])
    (by rw [scratch]; simp only [LeanExe.Extract.Core.ScalarRangePlan.func]; omega) bodyBound
  rw [scratch] at parsed
  simpa [LeanExe.Extract.Core.ScalarRangePlan.func] using parsed

end Project.Compiler.ArithmeticEncoding
