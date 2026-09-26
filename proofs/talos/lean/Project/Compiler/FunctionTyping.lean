import Project.Compiler.ArithmeticTyping
import Project.Compiler.SourceInvocation

namespace Project.Compiler.ArithmeticValidation

open Wasm.Binary
open Wasm.Binary.Validator
open Project.Compiler.ArithmeticEncoding
open Project.Compiler.ArithmeticModule
open LeanExe.Wasm.ScalarDescriptor

theorem i64_local_type (params extra index : Nat)
    (present : index < params + extra) (ib : index < 2 ^ 32) (eb : extra < 2 ^ 32) :
    localType (List.replicate params .i64) (Parsing.i64Locals extra) (UInt32.ofNat index) = some .i64 := by
  simp only [localType, List.length_replicate, UInt32.toNat_ofNat_of_lt' ib]
  by_cases ip : index < params
  · simp [ip]
  · have inExtra : index - params < extra := by omega
    simp only [ip, ite_false, Parsing.i64Locals, localDeclType, UInt32.toNat_ofNat_of_lt' eb,
      inExtra, ite_true]

theorem function_sequence (name : Lean.Name) (entry : String) (arity : Nat)
    {ir : LeanExe.IR.Expr} {descriptor : Expr}
    (recognized : Expr.ofIR ir = some descriptor) (arithmetic : descriptor.Arithmetic)
    (reads : ∀ index ∈ descriptor.reads, index < arity + 1 + descriptor.scratchWidth)
    (format : arity + 1 + descriptor.scratchWidth < 2 ^ 32) :
    Sequence (arity + 1 + descriptor.scratchWidth) [] [.i64]
      (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs 4
        (LeanExe.Extract.Core.scalarFunc name (some entry) arity ir)) := by
  rw [scalarFunc_emit _ _ _ _ _ _ recognized]
  have slot : arity < arity + 1 + descriptor.scratchWidth := by omega
  have encoded := arithmetic_typed arithmetic (arity + 1 + descriptor.scratchWidth)
    (arity + 1) reads (by omega) le_rfl
  exact encoded.append ((Sequence.set _ arity slot (by omega)).append
    (Sequence.get _ arity slot (by omega)))

/-- Validation of the complete user function from its derived typed encoding,
including the real parameter and local declarations and result frame. -/
theorem user_valid {func : LeanExe.IR.Func} {entry : String} {user : Code}
    (results : func.results.length = 1)
    (declared : user.locals = Parsing.i64Locals
      (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func))
    (localBound : func.params + (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func) < 2 ^ 32)
    (typed : ∀ (context : Context),
      Locals64 context (func.params + (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func)) →
      validateInstrs context [] 0 { values := [], polymorphic := false } 0 user.body =
        .ok { values := [.i64], polymorphic := false }) :
    validateFunction (rawModule func entry user) (typeValues func) 0
      { params := List.replicate func.params .i64, results := [.i64] } user = .ok () := by
  let context : Context :=
    { functionIndex := 0, functions := typeValues func
      locals := localType (List.replicate func.params .i64) user.locals
      globals := (rawModule func entry user).globals.map (·.type)
      labels := [[.i64]], results := [.i64]
      hasMemory := (rawModule func entry user).memories.length = 1 }
  have locals : Locals64 context
      (func.params + (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func)) := by
    intro index present
    change localType (List.replicate func.params .i64) user.locals (UInt32.ofNat index) = some .i64
    rw [declared]
    exact i64_local_type _ _ _ present (by omega) (by omega)
  change (do
    let state ← validateInstrs context [] 0 { values := [], polymorphic := false } 0 user.body
    let _ ← finishFrame context [] 0 { values := [], polymorphic := false } state [.i64]
    pure ()) = Except.ok ()
  rw [typed context locals]
  change (finishFrame context [] 0 { values := [], polymorphic := false }
    { values := [.i64], polymorphic := false } [.i64] >>= fun _ => pure ()) = Except.ok ()
  have finished := finish_i64 context [] []
  simp only [List.length_nil] at finished
  rw [finished]
  rfl

end Project.Compiler.ArithmeticValidation
