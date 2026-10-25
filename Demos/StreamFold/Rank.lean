import Demos.StreamFold.Control

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

variable {Acc : Type} {kernel : Kernel Acc}

abbrev Rank := Nat × Nat × Nat × Nat × Nat × Nat

abbrev rankOrder : WellFoundedRelation Rank :=
  Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel
    (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel))))

abbrev RankLt := rankOrder.rel

theorem rank_wellFounded : WellFounded RankLt := rankOrder.wf

def rank (unread zeroWrites : Ghost → Nat) (state : (BufferState Acc)) (ghost : Ghost) : Rank :=
  (unread ghost, if state.eof then 0 else 1, state.input.data.size - state.cursor.toNat,
    if state.line.size.toUInt64 == 0 then 0 else 1,
    state.output.data.size - state.written.toNat, zeroWrites ghost)

theorem rank_consumeInput (spec : KernelSpec kernel) (unread zeroWrites : Ghost → Nat) (ghost : Ghost)
    {state : (BufferState Acc)} (safe : Safe state) (empty : state.output.size = 0)
    (remaining : state.cursor < state.input.size) :
    RankLt (rank unread zeroWrites (consumeInput kernel state).state ghost)
      (rank unread zeroWrites state ghost) := by
  have next := consumeInput_safe spec safe
  have cursorLt := consumeInput_cursor spec safe empty remaining
  have cursorLe := next.1.cursor
  rw [next.2.1] at cursorLe
  have smaller : state.input.data.size - (consumeInput kernel state).state.cursor.toNat <
      state.input.data.size - state.cursor.toNat := by omega
  unfold rank
  rw [next.2.1, next.2.2]
  apply Prod.Lex.right
  apply Prod.Lex.right
  exact Prod.Lex.left _ _ smaller

theorem rank_completeLine (unread zeroWrites : Ghost → Nat) (ghost : Ghost)
    {state : (BufferState Acc)} (line : state.line.size.toUInt64 ≠ 0)
    (running : (completeLine kernel state).running = true) :
    RankLt (rank unread zeroWrites (completeLine kernel state).state ghost)
      (rank unread zeroWrites state ghost) := by
  cases parsed : (kernel state.total state.line).valid with
  | false => simp [completeLine, parsed] at running
  | true =>
    have lineFlag : (if state.line.size.toUInt64 == 0 then 0 else 1 : Nat) = 1 := by
      simp [line]
    simp only [completeLine, parsed, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simp only [rank, lineFlag]
    apply Prod.Lex.right
    apply Prod.Lex.right
    apply Prod.Lex.right
    exact Prod.Lex.left _ _ (show (0 : Nat) < 1 by decide)

theorem rank_afterRead (unread zeroWrites : Ghost → Nat) {before after : Ghost}
    {state : (BufferState Acc)} {bytes : Bytes} (eof : state.eof = false)
    (unreadLe : unread after ≤ unread before)
    (nonempty : bytes.data.size ≠ 0 → unread after < unread before) :
    RankLt (rank unread zeroWrites (afterRead state ⟨0, bytes⟩).state after)
      (rank unread zeroWrites state before) := by
  by_cases decreased : unread after < unread before
  · exact Prod.Lex.left _ _ decreased
  · have same : unread after = unread before := by omega
    have empty : bytes.data.size = 0 := by
      by_cases empty : bytes.data.size = 0
      · exact empty
      · exact False.elim (decreased (nonempty empty))
    have bytesSize : bytes.size = 0 := by simp [Bytes.size, empty]
    simp only [afterRead, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    unfold rank
    simp only [same, eof, bytesSize, beq_self_eq_true, ↓reduceIte]
    apply Prod.Lex.right
    exact Prod.Lex.left _ _ (show (0 : Nat) < 1 by decide)

theorem rank_afterWrite (unread zeroWrites : Ghost → Nat) {before after : Ghost}
    {state : (BufferState Acc)} (safe : Safe state) (pending : state.written < state.output.size)
    (count : UInt64) (bound : count.toNat ≤ (remainingOutput state).data.size)
    (same : unread after = unread before)
    (zero : count = 0 → zeroWrites after < zeroWrites before) :
    RankLt (rank unread zeroWrites (afterWrite state ⟨0, count⟩).state after)
      (rank unread zeroWrites state before) := by
  have pendingNat := UInt64.lt_iff_toNat_lt.mp pending
  rw [safe.output_toNat] at pendingNat
  rw [remainingOutput_size safe] at bound
  have sumBound : state.written.toNat + count.toNat ≤ state.output.data.size := by omega
  have sumNat : (state.written + count).toNat = state.written.toNat + count.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt sumBound safe.outputSize)]
  by_cases countZero : count = 0
  · have different : state.written ≠ state.output.size := by
      intro equal
      rw [equal] at pending
      exact (UInt64.lt_irrefl _) pending
    simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      countZero, UInt64.add_zero, beq_iff_eq, different]
    unfold rank
    rw [same]
    apply Prod.Lex.right
    apply Prod.Lex.right
    apply Prod.Lex.right
    apply Prod.Lex.right
    apply Prod.Lex.right
    exact zero countZero
  · have countPositive : 0 < count.toNat := by
      have nonzero : count.toNat ≠ 0 := by
        intro sameNat
        apply countZero
        exact UInt64.toNat_inj.mp (by simpa using sameNat)
      omega
    simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    split
    · unfold rank
      rw [same]
      apply Prod.Lex.right
      apply Prod.Lex.right
      apply Prod.Lex.right
      apply Prod.Lex.right
      exact Prod.Lex.left _ _ (Nat.sub_pos_of_lt pendingNat)
    · unfold rank
      rw [same]
      apply Prod.Lex.right
      apply Prod.Lex.right
      apply Prod.Lex.right
      apply Prod.Lex.right
      have smaller : state.output.data.size - (state.written + count).toNat <
          state.output.data.size - state.written.toNat := by rw [sumNat]; omega
      exact Prod.Lex.left _ _ smaller

end Demos.StreamFold

