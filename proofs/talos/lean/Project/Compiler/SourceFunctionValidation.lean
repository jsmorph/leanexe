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
  have readBound := extractScalarExpr_reads extracted recognized (count := arity)
    (by intro slot present; simpa using present)
  have reads : ∀ index ∈ descriptor.reads, index < arity + 1 + descriptor.scratchWidth := by
    intro index member
    have h := readBound index member
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
