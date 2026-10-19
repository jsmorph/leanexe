import Lean

/-! Finite tail runs: a step continues with another state or returns a value.  The natural
index counts continuing steps and occurs only in proofs. -/

namespace Verified.Tail

inductive Run (step : α → Sum α β) : α → β → Nat → Prop where
  | done {state value} (h : step state = .inr value) : Run step state value 0
  | next {state state' value n} (h : step state = .inl state')
      (rest : Run step state' value n) : Run step state value (n + 1)

theorem Run.unique {step : α → Sum α β} {state value value' n n'}
    (run : Run step state value n) (other : Run step state value' n') :
    value = value' ∧ n = n' := by
  induction run generalizing value' n' with
  | done h =>
    cases other with
    | done h' => exact ⟨Sum.inr.inj (h.symm.trans h'), rfl⟩
    | next h' _ => cases h.symm.trans h'
  | next h rest ih =>
    cases other with
    | done h' => cases h.symm.trans h'
    | next h' rest' =>
      cases Sum.inl.inj (h.symm.trans h')
      obtain ⟨rfl, rfl⟩ := ih rest'
      exact ⟨rfl, rfl⟩

theorem Run.eq_of_fixed {step : α → Sum α β} {meaning : α → β}
    (fixed : ∀ state, meaning state = (step state).elim meaning id)
    {state value n} (run : Run step state value n) : meaning state = value := by
  induction run with
  | @done state value h => simpa only [h, Sum.elim_inr, id_eq] using fixed state
  | @next state state' value n h rest ih =>
    have hs := fixed state
    rw [h] at hs
    exact hs.trans ih

theorem Run.exists_of_wellFounded {step : α → Sum α β} {rel : α → α → Prop}
    (wf : WellFounded rel)
    (decreases : ∀ state state', step state = .inl state' → rel state' state) :
    ∀ state, ∃ value n, Run step state value n := by
  intro state
  induction state using wf.induction with
  | h state ih =>
    cases hs : step state with
    | inl state' =>
      obtain ⟨value, n, run⟩ := ih state' (decreases state state' hs)
      exact ⟨value, n + 1, .next hs run⟩
    | inr value => exact ⟨value, 0, .done hs⟩

end Verified.Tail

#print axioms Verified.Tail.Run.unique
#print axioms Verified.Tail.Run.eq_of_fixed
#print axioms Verified.Tail.Run.exists_of_wellFounded
