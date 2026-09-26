import Project.Compiler.ArithmeticTyping
import Project.Compiler.TypedLoops
import LeanExe.Wasm.ScalarRangeAdmission

namespace Project.Compiler.ArithmeticValidation

open LeanExe.Wasm.ScalarDescriptor

/-- Typed encoding of the complete production range function. Every local read
is bounded statically; both branches of every scalar expression are included. -/
theorem range_function_sequence {descriptor : Range} {plan : LeanExe.Extract.Core.ScalarRangePlan}
    (matched : descriptor.Matches plan) (arithmetic : descriptor.All Expr.Arithmetic)
    (arity releaseIndex : Nat) (name : Lean.Name) (exportName : Option String)
    (reads : descriptor.All (fun e => ∀ index ∈ e.reads, index < arity + 3))
    (format : arity + 3 + descriptor.scratchWidth < 2 ^ 32) :
    Sequence (arity + 3 + descriptor.scratchWidth) [] [.i64]
      (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex (plan.func name exportName arity)) := by
  obtain ⟨ac, ai, astep, ar⟩ := arithmetic
  obtain ⟨bc, bi, bs, br⟩ := reads
  let count := arity + 3 + descriptor.scratchWidth
  have format' : count ≤ 2 ^ 32 := by dsimp [count]; omega
  have emitExpression {e : Expr} (a : e.Arithmetic) (b : ∀ index ∈ e.reads, index < arity + 3)
      (width : e.scratchWidth ≤ descriptor.scratchWidth) :
      Sequence count [] [.i64] (e.emit (arity + 3)) :=
    arithmetic_typed a count (arity + 3) (fun index member => Nat.lt_of_lt_of_le (b index member) (by dsimp [count]; omega))
      format' (by dsimp [count]; omega)
  have countTyped := emitExpression ac bc (by simp only [Range.scratchWidth]; omega)
  have initialTyped := emitExpression ai bi (by simp only [Range.scratchWidth]; omega)
  have stepTyped := emitExpression astep bs (by simp only [Range.scratchWidth]; omega)
  have resultTyped := emitExpression ar br (by simp only [Range.scratchWidth]; omega)
  have get (index : Nat) (bound : index < arity + 3) : Sequence count [] [.i64] [.localGet index] :=
    Sequence.get count index (by dsimp [count]; omega) (by dsimp [count] at format'; omega)
  have set (index : Nat) (bound : index < arity + 3) : Sequence count [.i64] [] [.localSet index] :=
    Sequence.set count index (by dsimp [count]; omega) (by dsimp [count] at format'; omega)
  have setupTyped : Sequence count [] [] ((descriptor.setup arity).emit (arity + 3)) := by
    simpa [Range.setup, Stmt.emit, Expr.emit, List.append_assoc] using
      (countTyped.append (set (arity + 2) (by omega))).append
        ((initialTyped.append (set arity (by omega))).append
          ((Sequence.const count 0).append (set (arity + 1) (by omega))))
  have conditionTyped : Sequence count [] [.i32] ((descriptor.loop arity).condition.emit (arity + 3)) := by
    exact (get (arity + 1) (by omega)).append
      (((get (arity + 2) (by omega)).frame [.i64]).append (Sequence.lt count))
  have bodyTyped : Sequence count [] [] ((descriptor.loop arity).body.emit (arity + 3)) := by
    have increment := (get (arity + 1) (by omega)).append
      (((Sequence.const count 1).frame [.i64]).append
        ((Sequence.operation count .add).append (set (arity + 1) (by omega))))
    simpa [Range.loop, Stmt.emit, Expr.emit, U64Op.instruction, BEq.beq, instBEqU64Op, instBEqU64Op.beq, U64Op.ctorIdx, List.append_assoc] using
      (stepTyped.append (set arity (by omega))).append increment
  have loopTyped : Sequence count [] [] ((descriptor.loop arity).emit (arity + 3)) :=
    conditionTyped.while bodyTyped
  rw [Range.func_emit matched]
  exact ((setupTyped.append loopTyped).append resultTyped).append
    ((set arity (by omega)).append (get arity (by omega)))

end Project.Compiler.ArithmeticValidation
