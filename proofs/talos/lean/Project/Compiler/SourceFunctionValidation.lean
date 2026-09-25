import Project.Compiler.FunctionTyping

namespace Project.Compiler.ArithmeticValidation

open LeanExe.Extract.Core
open LeanExe.Wasm.ScalarDescriptor
open Project.Compiler.Parsing
open Project.Compiler.ArithmeticModule
open Wasm.Binary

/-- The actual user body extracted from original arithmetic source passes the
existing function validator, rather than merely executing in the interpreter. -/
theorem extracted_function_valid
    {name : Lean.Name} {entry : String} {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name (some entry) type source = some func)
    (localBound : func.locals + LeanExe.Wasm.Binary.CoreWasm.funcScratch func < 2 ^ 32)
    (bodyBound : (LeanExe.Wasm.Binary.CoreWasm.localDecls func ++
      LeanExe.Wasm.Binary.CoreWasm.encodeInstrs
        (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs 4 func) ++ [11]).length < 2 ^ 32)
    (user : Code) (parsed : Parses code (LeanExe.Wasm.Binary.CoreWasm.emitFuncBody 4 func) user) :
    Validator.validateFunction (rawModule func entry user) (typeValues func) 0
      (typeValues func).head! user = .ok () := by
  simp only [extractScalarFunc, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
  obtain ⟨arity, _, body, _, ir, extracted, rfl⟩ := compiled
  obtain ⟨descriptor, recognized, arithmetic⟩ := extractScalarExpr_arithmetic extracted
  have scratch := scalarFunc_scratch arity name (some entry) recognized
  have format : arity + 1 + descriptor.scratchWidth < 2 ^ 32 := by
    rw [scratch] at localBound
    exact localBound
  let args : List UInt64 := List.replicate arity 0
  have supported := extractScalarExpr_supported extracted
  obtain ⟨value, sourceEval⟩ := supported.evaluates args.reverse (by simp [args])
  have argumentLocals : ScalarLocalsMatch (List.range arity).reverse args.reverse (args ++ [0]) := by
    simpa only [args, List.length_replicate] using scalarArgumentLocals args [0]
  have irEval := extractScalarExpr_correct sourceEval extracted argumentLocals
  have readBound := arithmetic.reads_bound (Expr.ofIR_eval irEval recognized).1
  have reads : ∀ index ∈ descriptor.reads, index < arity + 1 + descriptor.scratchWidth := by
    intro index member
    have h := readBound index member
    simp only [args, List.length_append, List.length_replicate, List.length_cons, List.length_nil] at h
    omega
  obtain ⟨raw, encoded, typed⟩ := function_sequence name entry arity recognized arithmetic reads format
  have parsedTyped := function_body 4 encoded
    (by simp [scalarFunc])
    (by rw [scratch]; simp only [scalarFunc]; omega) bodyBound
  have same := parsed.unique parsedTyped
  subst user
  apply user_valid (func := scalarFunc name (some entry) arity ir) rfl rfl
  · rw [scratch]
    simp only [scalarFunc]
    omega
  · intro context locals
    have localTypes : Locals64 context (arity + 1 + descriptor.scratchWidth) := by
      rw [scratch] at locals
      simpa [scalarFunc, Nat.add_assoc] using locals
    exact typed context localTypes [] 0 0 [] (Nat.le_refl 0)

end Project.Compiler.ArithmeticValidation
