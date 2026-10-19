import Lean

/-! Finite tail runs: a step continues with another state or returns a value.  The natural
index counts continuing steps and occurs only in proofs. -/

namespace Verified.Tail

inductive Run (step : α → Sum α β) : α → β → Nat → Prop where
  | done {state value} (h : step state = .inr value) : Run step state value 0
  | next {state state' value n} (h : step state = .inl state')
      (rest : Run step state' value n) : Run step state value (n + 1)

def rank (step : α → Sum α β)
    (wf : WellFounded (fun next state => step state = .inl next)) : α → Nat :=
  wf.fix fun state recur =>
    match h : step state with
    | .inl next => recur next h + 1
    | .inr _ => 0

theorem rank_eq (step : α → Sum α β)
    (wf : WellFounded (fun next state => step state = .inl next)) (state : α) :
    rank step wf state = (step state).elim (fun next => rank step wf next + 1) (fun _ => 0) := by
  unfold rank
  rw [WellFounded.fix_eq]
  cases h : step state <;> rfl

theorem Run.rank_eq {step : α → Sum α β}
    (wf : WellFounded (fun next state => step state = .inl next))
    {state value n} (run : Run step state value n) : rank step wf state = n := by
  induction run with
  | @done state value h => rw [Verified.Tail.rank_eq step wf state, h]; rfl
  | @next state state' value n h _ ih =>
    rw [Verified.Tail.rank_eq step wf state, h]
    exact congrArg (fun n => n + 1) ih

def costAt (step : α → Sum α β) (charge : α → Nat) : Nat → α → Nat
  | 0, _ => 0
  | fuel + 1, state =>
    charge state + (step state).elim (costAt step charge fuel) (fun _ => 0)

def fitsAt (step : α → Sum α β) (valid : α → Bool) : Nat → α → Bool
  | 0, _ => false
  | fuel + 1, state =>
    valid state && (step state).elim (fitsAt step valid fuel) (fun _ => true)

theorem Run.costAt_eq {step : α → Sum α β} (charge : α → Nat)
    {state value n} (run : Run step state value n) {fuel : Nat} (hf : n < fuel) :
    costAt step charge fuel state = costAt step charge (n + 1) state := by
  induction run generalizing fuel with
  | done h =>
    cases fuel with
    | zero => exact False.elim (Nat.not_lt_zero _ hf)
    | succ fuel => simp [costAt, h]
  | @next state state' value n h rest ih =>
    cases fuel with
    | zero => exact False.elim (Nat.not_lt_zero _ hf)
    | succ fuel =>
      simp only [costAt, h, Sum.elim_inl]
      exact congrArg (fun cost => charge state + cost) (ih (Nat.lt_of_succ_lt_succ hf))

theorem Run.fitsAt_eq {step : α → Sum α β} (valid : α → Bool)
    {state value n} (run : Run step state value n) {fuel : Nat} (hf : n < fuel) :
    fitsAt step valid fuel state = fitsAt step valid (n + 1) state := by
  induction run generalizing fuel with
  | done h =>
    cases fuel with
    | zero => exact False.elim (Nat.not_lt_zero _ hf)
    | succ fuel => simp [fitsAt, h]
  | @next state state' value n h rest ih =>
    cases fuel with
    | zero => exact False.elim (Nat.not_lt_zero _ hf)
    | succ fuel =>
      simp only [fitsAt, h, Sum.elim_inl]
      exact congrArg (fun fits => valid state && fits) (ih (Nat.lt_of_succ_lt_succ hf))

theorem Run.length_le {step : α → Sum α β} (rank : α → Nat)
    (decreases : ∀ state next, step state = .inl next → rank next < rank state)
    {state value n} (run : Run step state value n) : n ≤ rank state := by
  induction run with
  | done _ => exact Nat.zero_le _
  | next h rest ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (decreases _ _ h))

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

theorem costAt_rank_eq (step : α → Sum α β) (rank : α → Nat)
    (decreases : ∀ state next, step state = .inl next → rank next < rank state)
    (charge : α → Nat) (state : α) :
    costAt step charge (rank state + 1) state = charge state +
      (step state).elim (fun next => costAt step charge (rank next + 1) next) (fun _ => 0) := by
  rw [costAt]
  cases h : step state with
  | inr value => rfl
  | inl next =>
    simp only [Sum.elim_inl]
    obtain ⟨value, n, run⟩ := Run.exists_of_wellFounded (measure rank).wf decreases next
    have hn := run.length_le rank decreases
    have hlt := decreases state next h
    congr 1
    exact (run.costAt_eq charge (fuel := rank state) (by omega)).trans
      (run.costAt_eq charge (fuel := rank next + 1) (by omega)).symm

theorem fitsAt_rank_eq (step : α → Sum α β) (rank : α → Nat)
    (decreases : ∀ state next, step state = .inl next → rank next < rank state)
    (valid : α → Bool) (state : α) :
    fitsAt step valid (rank state + 1) state = (valid state &&
      (step state).elim (fun next => fitsAt step valid (rank next + 1) next) (fun _ => true)) := by
  rw [fitsAt]
  cases h : step state with
  | inr value => simp
  | inl next =>
    simp only [Sum.elim_inl]
    obtain ⟨value, n, run⟩ := Run.exists_of_wellFounded (measure rank).wf decreases next
    have hn := run.length_le rank decreases
    have hlt := decreases state next h
    congr 1
    exact (run.fitsAt_eq valid (fuel := rank state) (by omega)).trans
      (run.fitsAt_eq valid (fuel := rank next + 1) (by omega)).symm

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

end Verified.Tail

#print axioms Verified.Tail.Run.unique
#print axioms Verified.Tail.Run.eq_of_fixed
#print axioms Verified.Tail.Run.exists_of_wellFounded
#print axioms Verified.Tail.rank_eq
#print axioms Verified.Tail.Run.length_le
#print axioms Verified.Tail.costAt_rank_eq
#print axioms Verified.Tail.fitsAt_rank_eq
