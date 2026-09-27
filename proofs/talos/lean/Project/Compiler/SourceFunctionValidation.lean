import LeanExe.Wasm.ScalarSequenceAdmission
import Project.Compiler.SequenceFunctionBytes
import LeanExe.Wasm.ScalarWordRangeAdmission
import LeanExe.Wasm.ScalarPublicAdmission
import Project.Compiler.FunctionTyping
import Project.Compiler.RangeTyping
import Project.Compiler.RangeExitTyping

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
  obtain ⟨arity, result, body, signature, _, _, branches⟩ := extractScalarFunc_cases compiled
  rcases branches with ⟨ir, extracted, rfl⟩ | ⟨rfl, plan, extracted, rfl⟩ | ⟨rfl, plan, extracted, rfl⟩ | ⟨rfl, plan, extracted, rfl⟩ | ⟨rfl, plan, extracted, rfl⟩ | ⟨rfl, plan, extracted, rfl⟩
  · obtain ⟨descriptor, recognized, arithmetic, readBound⟩ := extractScalarPublic_admitted extracted
    have scratch := scalarFunc_scratch arity name (some entry) recognized
    have format : arity + 1 + descriptor.scratchWidth < 2 ^ 32 := by
      rw [scratch] at localBound
      exact localBound
    have inputLen := scalarSignature_inputs_length signature
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
  · obtain ⟨descriptor, matched, arithmetic, reads⟩ := extractScalarRangePublic_admitted extracted
      (scalarSignature_inputs_length signature)
    have scratch := Range.func_scratch matched arity name (some entry)
    have format : arity + 3 + descriptor.scratchWidth < 2 ^ 32 := by
      rw [scratch] at localBound
      exact localBound
    obtain ⟨raw, encoded, typed⟩ := range_function_sequence matched arithmetic arity 4 name (some entry) reads format
    have parsedTyped := function_body 4 encoded
      (by simp [ScalarRangePlan.func])
      (by rw [scratch]; simp only [ScalarRangePlan.func]; omega) bodyBound
    have same := parsed.unique parsedTyped
    subst user
    apply user_valid (func := plan.func name (some entry) arity) rfl rfl
    · rw [scratch]
      simp only [ScalarRangePlan.func]
      omega
    · intro context locals
      have localTypes : Locals64 context (arity + 3 + descriptor.scratchWidth) := by
        rw [scratch] at locals
        simpa [ScalarRangePlan.func, Nat.add_assoc] using locals
      exact typed context localTypes [] 0 0 [] (Nat.le_refl 0)
  · obtain ⟨descriptor, matched, arithmetic, reads⟩ := extractScalarRangeExitPublic_admitted extracted
      (scalarSignature_inputs_length signature)
    have scratch := RangeExit.func_scratch matched arity name (some entry)
    have format : arity + 4 + descriptor.scratchWidth < 2 ^ 32 := by
      rw [scratch] at localBound
      exact localBound
    obtain ⟨raw, encoded, typed⟩ := range_exit_function_sequence matched arithmetic arity 4 name (some entry) reads format
    have parsedTyped := function_body 4 encoded
      (by simp [ScalarRangeExitPlan.func])
      (by rw [scratch]; simp only [ScalarRangeExitPlan.func]; omega) bodyBound
    have same := parsed.unique parsedTyped
    subst user
    apply user_valid (func := plan.func name (some entry) arity) rfl rfl
    · rw [scratch]
      simp only [ScalarRangeExitPlan.func]
      omega
    · intro context locals
      have localTypes : Locals64 context (arity + 4 + descriptor.scratchWidth) := by
        rw [scratch] at locals
        simpa [ScalarRangeExitPlan.func, Nat.add_assoc] using locals
      exact typed context localTypes [] 0 0 [] (Nat.le_refl 0)
  · obtain ⟨descriptor, matched, arithmetic, reads⟩ := extractScalarBooleanRangePublic_admitted extracted
      (scalarSignature_inputs_length signature)
    have scratch := RangeExit.func_scratch matched arity name (some entry)
    have format : arity + 4 + descriptor.scratchWidth < 2 ^ 32 := by
      rw [scratch] at localBound
      exact localBound
    obtain ⟨raw, encoded, typed⟩ := range_exit_function_sequence matched arithmetic arity 4 name (some entry) reads format
    have parsedTyped := function_body 4 encoded
      (by simp [ScalarRangeExitPlan.func])
      (by rw [scratch]; simp only [ScalarRangeExitPlan.func]; omega) bodyBound
    have same := parsed.unique parsedTyped
    subst user
    apply user_valid (func := plan.func name (some entry) arity) rfl rfl
    · rw [scratch]
      simp only [ScalarRangeExitPlan.func]
      omega
    · intro context locals
      have localTypes : Locals64 context (arity + 4 + descriptor.scratchWidth) := by
        rw [scratch] at locals
        simpa [ScalarRangeExitPlan.func, Nat.add_assoc] using locals
      exact typed context localTypes [] 0 0 [] (Nat.le_refl 0)
  · obtain ⟨descriptor, matched, arithmetic, reads⟩ := extractScalarWordRangePublic_admitted extracted
      (scalarSignature_inputs_length signature)
    have scratch := RangeExit.func_scratch matched arity name (some entry)
    have format : arity + 4 + descriptor.scratchWidth < 2 ^ 32 := by
      rw [scratch] at localBound
      exact localBound
    obtain ⟨raw, encoded, typed⟩ := range_exit_function_sequence matched arithmetic arity 4 name (some entry) reads format
    have parsedTyped := function_body 4 encoded
      (by simp [ScalarRangeExitPlan.func])
      (by rw [scratch]; simp only [ScalarRangeExitPlan.func]; omega) bodyBound
    have same := parsed.unique parsedTyped
    subst user
    apply user_valid (func := plan.func name (some entry) arity) rfl rfl
    · rw [scratch]
      simp only [ScalarRangeExitPlan.func]
      omega
    · intro context locals
      have localTypes : Locals64 context (arity + 4 + descriptor.scratchWidth) := by
        rw [scratch] at locals
        simpa [ScalarRangeExitPlan.func, Nat.add_assoc] using locals
      exact typed context localTypes [] 0 0 [] (Nat.le_refl 0)
  · obtain ⟨descriptor, matched, arithmetic, reads⟩ := extractScalarSequencePublic_admitted extracted
      (scalarSignature_inputs_length signature)
    have nonempty := plan.width_pos
    have scratch := matched.func_scratch arity name (some entry)
    have format : arity + plan.width + descriptor.scratchWidth < 2 ^ 32 := by
      rw [scratch] at localBound
      exact localBound
    obtain ⟨raw, encoded, typed⟩ := loop_sequence_function_sequence matched arithmetic arity 4 name (some entry) reads format
    have parsedTyped := function_body 4 encoded
      (by simp [ScalarSequencePlan.func, plan.width_pos])
      (by rw [scratch]; simp only [ScalarSequencePlan.func]; omega) bodyBound
    have same := parsed.unique parsedTyped
    subst user
    apply user_valid (func := plan.func name (some entry) arity) rfl rfl
    · rw [scratch]
      simp only [ScalarSequencePlan.func]
      omega
    · intro context locals
      have localTypes : Locals64 context (arity + plan.width + descriptor.scratchWidth) := by
        rw [scratch] at locals
        simpa [ScalarSequencePlan.func, Nat.add_assoc] using locals
      exact typed context localTypes [] 0 0 [] (Nat.le_refl 0)

end Project.Compiler.ArithmeticValidation
