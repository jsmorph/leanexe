import Verified.Bound

namespace Verified

/-- A bound on the cost of a loop whose condition costs nothing and whose passes each cost at most
`c`, except one pass that costs at most `last` and after which the condition fails.  `P n s`
states what holds of the state `s` with `n` passes left. -/
theorem loopCost_le_last {α : Type} {C : α → Bool} {BA : UInt64 → α → Nat}
    {F : UInt64 → α → α} (P : Nat → α → Prop) (c last : Nat)
    (pass : ∀ n i s, P (n + 1) s → C s = true →
      (BA i s ≤ c ∧ P n (F i s)) ∨ (BA i s ≤ last ∧ C (F i s) = false)) :
    ∀ (n : Nat) (i : UInt64) (s : α), P n s →
      loopCost (fun _ => 0) C BA F n i s ≤ n * c + last
  | 0, _, _, _ => by simp [loopCost]
  | n + 1, i, s, holds => by
    simp only [loopCost, Nat.zero_add]
    cases condition : C s with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      rcases pass n i s holds condition with ⟨cheap, kept⟩ | ⟨costly, stops⟩
      · have rest := loopCost_le_last P c last pass n (i + 1) (F i s) kept
        rw [Nat.succ_mul]
        omega
      · have rest : loopCost (fun _ => 0) C BA F n (i + 1) (F i s) = 0 := by
          cases n <;> simp [loopCost, stops]
        omega

end Verified
