import Project.Compiler.ArithmeticTyping
import Project.Compiler.TypedLoops
import LeanExe.Wasm.ScalarRangeExitAdmission

namespace Project.Compiler.ArithmeticValidation

open LeanExe.Wasm.ScalarDescriptor

/-- Typed encoding of the complete production range function. Every local read
is bounded statically; both branches of every scalar expression are included. -/
theorem range_exit_function_sequence {descriptor : RangeExit} {plan : LeanExe.Extract.Core.ScalarRangeExitPlan}
    (matched : descriptor.Matches plan) (arithmetic : descriptor.All Expr.Arithmetic)
    (arity releaseIndex : Nat) (name : Lean.Name) (exportName : Option String)
    (reads : descriptor.All (fun e => ∀ index ∈ e.reads, index < arity + 3))
    (format : arity + 4 + descriptor.scratchWidth < 2 ^ 32) :
    Sequence (arity + 4 + descriptor.scratchWidth) [] [.i64]
      (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex (plan.func name exportName arity)) := by
  obtain ⟨ac, ai, astep, adone, ar⟩ := arithmetic
  obtain ⟨bc, bi, bs, bd, br⟩ := reads
  let count := arity + 4 + descriptor.scratchWidth
  have format' : count ≤ 2 ^ 32 := by dsimp [count]; omega
  have emitExpression {e : Expr} (a : e.Arithmetic) (b : ∀ index ∈ e.reads, index < arity + 3)
      (width : e.scratchWidth ≤ descriptor.scratchWidth) :
      Sequence count [] [.i64] (e.emit (arity + 4)) :=
    arithmetic_typed a count (arity + 4) (fun index member => Nat.lt_of_lt_of_le (b index member) (by dsimp [count]; omega))
      format' (by dsimp [count]; omega)
  have countTyped := emitExpression ac bc (by simp only [RangeExit.scratchWidth]; omega)
  have initialTyped := emitExpression ai bi (by simp only [RangeExit.scratchWidth]; omega)
  have stepTyped := emitExpression astep bs (by simp only [RangeExit.scratchWidth]; omega)
  have doneTyped := emitExpression adone bd (by simp only [RangeExit.scratchWidth]; omega)
  have resultTyped := emitExpression ar br (by simp only [RangeExit.scratchWidth]; omega)
  have get (index : Nat) (bound : index < arity + 4) : Sequence count [] [.i64] [.localGet index] :=
    Sequence.get count index (by dsimp [count]; omega) (by dsimp [count] at format'; omega)
  have set (index : Nat) (bound : index < arity + 4) : Sequence count [.i64] [] [.localSet index] :=
    Sequence.set count index (by dsimp [count]; omega) (by dsimp [count] at format'; omega)
  have setupTyped : Sequence count [] [] ((descriptor.setup arity).emit (arity + 4)) := by
    simpa [RangeExit.setup, Stmt.emit, Expr.emit, List.append_assoc] using
      (countTyped.append (set (arity + 2) (by omega))).append
        ((initialTyped.append (set arity (by omega))).append
          (((Sequence.const count 0).append (set (arity + 1) (by omega))).append
            ((Sequence.const count 0).append (set (arity + 3) (by omega)))))
  have conditionTyped : Sequence count [] [.i32] ((descriptor.loop arity).condition.emit (arity + 4)) := by
    exact (get (arity + 1) (by omega)).append
      (((get (arity + 2) (by omega)).frame [.i64]).append (Sequence.lt count))
  have indexArithmetic : (RangeExit.index arity).Arithmetic :=
    .choose .eq .get .const (.bin .get .const) .get
  have indexTyped : Sequence count [] [.i64] ((RangeExit.index arity).emit (arity + 4)) :=
    arithmetic_typed indexArithmetic count (arity + 4) (by
      intro index member
      simp [RangeExit.index, Expr.reads, LeanExe.Wasm.ScalarDescriptor.Cond.reads] at member
      rcases member with rfl | rfl | rfl <;> dsimp [count] <;> omega)
      format' (by
        simp [RangeExit.index, Expr.scratchWidth, LeanExe.Wasm.ScalarDescriptor.Cond.scratchWidth,
          BEq.beq, instBEqU64Op, instBEqU64Op.beq, U64Op.ctorIdx]
        dsimp [count]; omega)
  have bodyTyped : Sequence count [] [] ((descriptor.loop arity).body.emit (arity + 4)) := by
    simpa [RangeExit.loop, Stmt.emit, List.append_assoc] using
      (doneTyped.append (set (arity + 3) (by omega))).append
        ((stepTyped.append (set arity (by omega))).append (indexTyped.append (set (arity + 1) (by omega))))
  have loopTyped : Sequence count [] [] ((descriptor.loop arity).emit (arity + 4)) :=
    conditionTyped.while bodyTyped
  rw [RangeExit.func_emit matched]
  exact ((setupTyped.append loopTyped).append resultTyped).append
    ((set arity (by omega)).append (get arity (by omega)))

end Project.Compiler.ArithmeticValidation
