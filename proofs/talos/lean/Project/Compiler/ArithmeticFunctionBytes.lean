import Project.Compiler.ArithmeticEmission
import Project.Compiler.ArithmeticTranslation
import Project.Compiler.StructuredParsing
import Project.Compiler.ScalarFunction

namespace Project.Compiler.ArithmeticEncoding

open LeanExe.Wasm.ScalarDescriptor

/-- Encoding coverage for the full production function instruction stream,
including the result-slot store and load. -/
theorem scalar_function_encodable (name : Lean.Name) (exportName : Option String)
    (arity releaseIndex : Nat) {ir : LeanExe.IR.Expr} {descriptor : Expr}
    (recognized : Expr.ofIR ir = some descriptor) (arithmetic : descriptor.Arithmetic)
    (reads : ∀ index ∈ descriptor.reads, index < 2 ^ 32)
    (room : arity + 1 + descriptor.scratchWidth ≤ 2 ^ 32) :
    Encodable (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex
      (LeanExe.Extract.Core.scalarFunc name exportName arity ir)) := by
  rw [scalarFunc_emit _ _ _ _ _ _ recognized]
  have slot : arity < 2 ^ 32 := by omega
  exact (arithmetic_encodable arithmetic (arity + 1) reads room).append
    ((Encodable.atom (.set arity slot)).append (.atom (.get arity slot)))

/-- The complete production instruction bytes decode to a program with exactly
the established source behavior. Module sections and exported invocation are
separate obligations; this theorem does not claim them. -/
theorem scalar_function_bytes_execution (args : List UInt64) (name : Lean.Name)
    (exportName : Option String) (releaseIndex : Nat)
    {ir : LeanExe.IR.Expr} {descriptor : Expr} {value : UInt64}
    (recognized : Expr.ofIR ir = some descriptor) (arithmetic : descriptor.Arithmetic)
    (evaluated : ir.ScalarEval (args ++ [0]) value (args ++ [0]))
    (room : args.length + 1 + descriptor.scratchWidth ≤ 2 ^ 32)
    (m : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α) :
    let func := LeanExe.Extract.Core.scalarFunc name exportName args.length ir
    ∃ (raw : List Wasm.Binary.Instr) (next : Project.ProofKit.ScalarTransition.State),
      Parsing.Parses Wasm.Binary.expression
        (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs
          (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex func) ++ [11]) raw ∧
      Wasm.wp m (Wasm.Binary.Instr.listToTalos raw)
        (fun outcome => outcome = .Fallthrough store (next.toLocals [.i64 value]))
        store ((ScalarLowering.functionState func args).toLocals []) env := by
  dsimp only
  have readSlots := arithmetic.reads_bound (Expr.ofIR_eval evaluated recognized).1
  have reads : ∀ index ∈ descriptor.reads, index < 2 ^ 32 := by
    intro index member
    have h := readSlots index member
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    omega
  obtain ⟨raw, encoded⟩ := scalar_function_encodable name exportName args.length
    releaseIndex recognized arithmetic reads room
  obtain ⟨code, next, lowered, executed⟩ := ScalarLowering.scalar_function_execution args
    name exportName releaseIndex recognized evaluated m env store
  obtain ⟨translated, ht, related⟩ := encoded.translation
  have same : translated = code := Option.some.inj (ht.symm.trans lowered)
  subst translated
  exact ⟨raw, next, encoded.expression_parses, (related.wp_iff m store _ env _).mpr executed⟩

end Project.Compiler.ArithmeticEncoding
