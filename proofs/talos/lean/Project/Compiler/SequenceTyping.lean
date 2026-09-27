import Project.Compiler.RangeExitTyping
import LeanExe.Wasm.ScalarSequenceAdmission

namespace Project.Compiler.ArithmeticValidation
open LeanExe.Wasm.ScalarDescriptor

/-- Each loop body is typed within the complete sequence's shared scratch allocation. -/
theorem range_exit_body_sequence (descriptor : RangeExit) (arithmetic : descriptor.All Expr.Arithmetic)
    (slot scratch count : Nat)
    (reads : descriptor.All (fun e => ∀ index ∈ e.reads, index < scratch))
    (localsBound : slot + 4 ≤ scratch) (room : scratch + descriptor.scratchWidth ≤ count)
    (format : count ≤ 2 ^ 32) :
    Sequence count [] [] ((descriptor.program slot).emit scratch) := by
  obtain ⟨ac, ai, astep, adone, ar⟩ := arithmetic
  obtain ⟨bc, bi, bs, bd, br⟩ := reads
  have emitExpression {e : Expr} (a : e.Arithmetic) (b : ∀ index ∈ e.reads, index < scratch)
      (width : e.scratchWidth ≤ descriptor.scratchWidth) :
      Sequence count [] [.i64] (e.emit scratch) :=
    arithmetic_typed a count scratch (fun index member => Nat.lt_of_lt_of_le (b index member) (by omega))
      format (by omega)
  have countTyped := emitExpression ac bc (by simp only [RangeExit.scratchWidth]; omega)
  have initialTyped := emitExpression ai bi (by simp only [RangeExit.scratchWidth]; omega)
  have stepTyped := emitExpression astep bs (by simp only [RangeExit.scratchWidth]; omega)
  have doneTyped := emitExpression adone bd (by simp only [RangeExit.scratchWidth]; omega)
  have resultTyped := emitExpression ar br (by simp only [RangeExit.scratchWidth]; omega)
  have get (index : Nat) (bound : index < scratch) : Sequence count [] [.i64] [.localGet index] :=
    Sequence.get count index (by omega) (by omega)
  have set (index : Nat) (bound : index < scratch) : Sequence count [.i64] [] [.localSet index] :=
    Sequence.set count index (by omega) (by omega)
  have setupTyped : Sequence count [] [] ((descriptor.setup slot).emit scratch) := by
    simpa [RangeExit.setup, Stmt.emit, Expr.emit, List.append_assoc] using
      (countTyped.append (set (slot + 2) (by omega))).append
        ((initialTyped.append (set slot (by omega))).append
          (((Sequence.const count 0).append (set (slot + 1) (by omega))).append
            ((Sequence.const count 0).append (set (slot + 3) (by omega)))))
  have conditionTyped : Sequence count [] [.i32] ((descriptor.loop slot).condition.emit scratch) := by
    exact (get (slot + 1) (by omega)).append
      (((get (slot + 2) (by omega)).frame [.i64]).append (Sequence.lt count))
  have indexArithmetic : (RangeExit.index slot).Arithmetic :=
    .choose .eq .get .const (.bin .get .const) .get
  have indexTyped : Sequence count [] [.i64] ((RangeExit.index slot).emit scratch) :=
    arithmetic_typed indexArithmetic count scratch (by
      intro index member
      simp [RangeExit.index, Expr.reads, LeanExe.Wasm.ScalarDescriptor.Cond.reads] at member
      rcases member with rfl | rfl | rfl <;> omega)
      format (by
        simp [RangeExit.index, Expr.scratchWidth, LeanExe.Wasm.ScalarDescriptor.Cond.scratchWidth,
          BEq.beq, instBEqU64Op.beq, U64Op.ctorIdx]
        omega)
  have bodyTyped : Sequence count [] [] ((descriptor.loop slot).body.emit scratch) := by
    simpa [RangeExit.loop, Stmt.emit, List.append_assoc] using
      (doneTyped.append (set (slot + 3) (by omega))).append
        ((stepTyped.append (set slot (by omega))).append (indexTyped.append (set (slot + 1) (by omega))))
  have loopTyped : Sequence count [] [] ((descriptor.loop slot).emit scratch) :=
    conditionTyped.while bodyTyped
  simpa [RangeExit.program, RangeExit.setup, Program.emit, Stmt.emit, Expr.emit, List.append_assoc] using
    ((setupTyped.append loopTyped).append resultTyped).append (set slot (by omega))


/-- Every emitted loop in a sequence has bounded local accesses and a balanced stack. -/
theorem loop_sequence_body_sequence (descriptor : LoopSequence)
    (arithmetic : descriptor.All Expr.Arithmetic) (slot scratch count : Nat)
    (reads : descriptor.All (fun e => ∀ index ∈ e.reads, index < scratch))
    (localsBound : slot + descriptor.width ≤ scratch)
    (room : scratch + descriptor.scratchWidth ≤ count) (format : count ≤ 2 ^ 32) :
    Sequence count [] [] ((descriptor.program slot).emit scratch) := by
  induction descriptor generalizing slot with
  | leaf descriptor => exact range_exit_body_sequence descriptor arithmetic slot scratch count reads localsBound room format
  | bind first second firstIH secondIH =>
    have localsBound' : slot + (first.width + second.width) ≤ scratch := localsBound
    have room' : scratch + max first.scratchWidth second.scratchWidth ≤ count := room
    exact (firstIH arithmetic.1 slot reads.1 (by omega) (by omega)).append
      (secondIH arithmetic.2 (slot + first.width) reads.2 (by omega) (by omega))

/-- The full sequence function is typed, including its public result-slot copy. -/
theorem loop_sequence_function_sequence {descriptor : LoopSequence} {plan : LeanExe.Extract.Core.ScalarSequencePlan}
    (matched : descriptor.Matches plan) (arithmetic : descriptor.All Expr.Arithmetic)
    (arity releaseIndex : Nat) (name : Lean.Name) (exportName : Option String)
    (reads : descriptor.All (fun e => ∀ index ∈ e.reads, index < arity + plan.width))
    (format : arity + plan.width + descriptor.scratchWidth < 2 ^ 32) :
    Sequence (arity + plan.width + descriptor.scratchWidth) [] [.i64]
      (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex (plan.func name exportName arity)) := by
  let count := arity + plan.width + descriptor.scratchWidth
  have body := loop_sequence_body_sequence descriptor arithmetic arity (arity + plan.width) count reads
    (by rw [matched.width]) (Nat.le_refl _) (by dsimp [count]; omega)
  have resultBounds := plan.resultSlot_bounds arity
  have nonempty := plan.width_pos
  have getResult := Sequence.get count (plan.resultSlot arity) (by dsimp [count]; omega) (by omega)
  have setResult := Sequence.set count arity (by dsimp [count]; omega) (by omega)
  have returnResult := Sequence.get count arity (by dsimp [count]; omega) (by omega)
  rw [matched.func_emit]
  exact body.append (getResult.append (setResult.append returnResult))

end Project.Compiler.ArithmeticValidation
