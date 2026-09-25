import Project.Compiler.TypedConditionals

namespace Project.Compiler.ArithmeticValidation

open LeanExe.Wasm.ScalarDescriptor

theorem comparison_typed (op : LeanExe.Source.Scalar.Comparison) (a b : Expr)
    (count scratch : Nat) (left : Sequence count [] [.i64] (a.emit scratch))
    (right : Sequence count [] [.i64] (b.emit scratch)) :
    Sequence count [] [.i32] ((comparison op a b).emit scratch) := by
  induction op with
  | eq | beq => simpa [comparison, Cond.emit, List.append_assoc] using left.append ((right.frame [.i64]).append (Sequence.eq count))
  | lt => simpa [comparison, Cond.emit, List.append_assoc] using left.append ((right.frame [.i64]).append (Sequence.lt count))
  | le => simpa [comparison, Cond.emit, List.append_assoc] using left.append ((right.frame [.i64]).append (Sequence.le count))
  | gt =>
    simpa [comparison, Cond.emit, List.append_assoc] using (left.append ((right.frame [.i64]).append (Sequence.le count))).append
      (Sequence.eqz32 count)
  | ge =>
    simpa [comparison, Cond.emit, List.append_assoc] using (left.append ((right.frame [.i64]).append (Sequence.lt count))).append
      (Sequence.eqz32 count)
  | ne | bne =>
    simpa [comparison, Cond.emit, List.append_assoc] using (left.append ((right.frame [.i64]).append (Sequence.eq count))).append
      (Sequence.eqz32 count)
  | negate op ih => simpa [comparison, Cond.emit] using ih.append (Sequence.eqz32 count)

theorem checked_tail (count scratch : Nat) (op : U64Op) (zero : List LeanExe.Wasm.Instr)
    (zeroTyped : Sequence count [] [.i64] zero)
    (slot : scratch + 1 < count) (format : count ≤ 2 ^ 32) :
    Sequence count [] [.i64]
      [.localGet (scratch + 1), .constI64 0, .eqI64,
       .iff true zero (some [.localGet scratch, .localGet (scratch + 1), op.instruction])] := by
  have getFirst := Sequence.get count scratch (by omega) (by omega)
  have getSecond := Sequence.get count (scratch + 1) slot (by omega)
  have nonzero := getFirst.append ((getSecond.frame [.i64]).append (Sequence.operation count op))
  exact getSecond.append (((Sequence.const count 0).frame [.i64]).append
    ((Sequence.eq count).append (zeroTyped.if64 nonzero)))

/-- Every admitted arithmetic descriptor's actual emitted instruction sequence
has the required stack type in every context containing its i64 locals. -/
theorem arithmetic_typed {e : Expr} (arithmetic : e.Arithmetic) (count scratch : Nat)
    (reads : ∀ index ∈ e.reads, index < count)
    (format : count ≤ 2 ^ 32) (room : scratch + e.scratchWidth ≤ count) :
    Sequence count [] [.i64] (e.emit scratch) := by
  induction arithmetic generalizing scratch with
  | @get index =>
    have present := reads index (by simp [Expr.reads])
    exact Sequence.get count index present (by omega)
  | const => exact Sequence.const _ _
  | @bin left right op al ar ihl ihr =>
    have leftReads : ∀ index ∈ left.reads, index < count := by
      intro index member
      exact reads index (by simp [Expr.reads, member])
    have rightReads : ∀ index ∈ right.reads, index < count := by
      intro index member
      exact reads index (by simp [Expr.reads, member])
    by_cases checked : (op == .divU || op == .remU) = true
    · have capacity : scratch + (max left.scratchWidth right.scratchWidth + 2) ≤ count := by
        simpa only [Expr.scratchWidth, checked, ite_true] using room
      have first : scratch < count := by omega
      have slot : scratch + 1 < count := by omega
      have l := ihl (scratch + 2) leftReads (by omega)
      have r := ihr (scratch + 2) rightReads (by omega)
      have zero : Sequence count [] [.i64]
          (if op == .divU then [.constI64 0] else [.localGet scratch]) := by
        split
        · exact Sequence.const _ _
        · exact Sequence.get _ _ first (by omega)
      simpa only [Expr.emit, checked, ite_true, List.append_assoc] using
        ((l.append (Sequence.set count scratch first (by omega))).append
          ((r.append (Sequence.set count (scratch + 1) slot (by omega))).append
            (checked_tail count scratch op _ zero slot format)))
    · have capacity : scratch + max left.scratchWidth right.scratchWidth ≤ count := by
        simpa only [Expr.scratchWidth, checked, Bool.false_eq_true, ite_false] using room
      have l := ihl scratch leftReads (by omega)
      have r := ihr scratch rightReads (by omega)
      simpa only [Expr.emit, checked, Bool.false_eq_true, ite_false, List.append_assoc] using
        l.append ((r.frame [.i64]).append (Sequence.operation count op))
  | @choose a b t e op aa ab aTrue ae iha ihb iht ihe =>
    have ra : ∀ index ∈ a.reads, index < count := by
      intro index member; exact reads index (by simp [Expr.reads, member])
    have rb : ∀ index ∈ b.reads, index < count := by
      intro index member; exact reads index (by simp [Expr.reads, member])
    have rt : ∀ index ∈ t.reads, index < count := by
      intro index member; exact reads index (by simp [Expr.reads, member])
    have re : ∀ index ∈ e.reads, index < count := by
      intro index member; exact reads index (by simp [Expr.reads, member])
    simp only [Expr.scratchWidth, comparison_scratch] at room
    exact (comparison_typed op a b count scratch
      (iha scratch ra (by omega)) (ihb scratch rb (by omega))).append
      ((iht scratch rt (by omega)).if64 (ihe scratch re (by omega)))

end Project.Compiler.ArithmeticValidation
