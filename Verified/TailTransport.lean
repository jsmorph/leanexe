import Verified.TailRun

namespace Verified.Tail

def withFixed (step : α → β → Sum β γ) (state : α × β) : Sum (α × β) γ :=
  Sum.map (fun next => (state.1, next)) id (step state.1 state.2)

theorem withFixed_wellFounded (step : α → β → Sum β γ)
    (wf : ∀ fixed, WellFounded (fun next state => step fixed state = .inl next)) :
    WellFounded (fun next state => withFixed step state = .inl next) := by
  have key : ∀ fixed state, Acc (fun next state => withFixed step state = .inl next)
      (fixed, state) := by
    intro fixed state
    induction state using (wf fixed).induction with
    | h state ih =>
      refine Acc.intro _ ?_
      rintro ⟨fixed', next⟩ hn
      cases hs : step fixed state with
      | inr value => simp [withFixed, hs] at hn
      | inl next' =>
        simp only [withFixed, hs, Sum.map_inl, Sum.inl.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        exact ih _ hs
  exact ⟨fun ⟨fixed, state⟩ => key fixed state⟩

theorem rank_lt {step : α → Sum α β}
    (wf : WellFounded (fun next state => step state = .inl next))
    {state next : α} (h : step state = .inl next) : rank step wf next < rank step wf state := by
  rw [rank_eq step wf state, h]
  exact Nat.lt_succ_self _

theorem Run.map {step : α → Sum α β} {target : γ → Sum γ δ} (φ : α → γ) (ψ : β → δ)
    (commute : ∀ state, target (φ state) = Sum.map φ ψ (step state))
    {state value n} (run : Run step state value n) : Run target (φ state) (ψ value) n := by
  induction run with
  | done h => exact .done (by rw [commute, h]; rfl)
  | next h _ ih => exact .next (by rw [commute, h]; rfl) ih

theorem withFixed_rank (step : α → β → Sum β γ)
    (wf : ∀ fixed, WellFounded (fun next state => step fixed state = .inl next))
    (fixed : α) (state : β) :
    rank (withFixed step) (withFixed_wellFounded step wf) (fixed, state) =
      rank (step fixed) (wf fixed) state := by
  obtain ⟨value, n, run⟩ := Run.exists_of_wellFounded (wf fixed) (fun _ _ h => h) state
  have mapped := run.map (target := withFixed step) (fun state => (fixed, state)) id (fun _ => rfl)
  exact (mapped.rank_eq _).trans (run.rank_eq _).symm

theorem decreases_transport {step : α → Sum α β} {target : γ → Sum γ δ}
    (φ : α → γ) (θ : γ → α) (ψ : β → δ)
    (left : ∀ state, θ (φ state) = state) (right : ∀ state, φ (θ state) = state)
    (commute : ∀ state, target (φ state) = Sum.map φ ψ (step state))
    (measure : α → Nat)
    (decreases : ∀ state next, step state = .inl next → measure next < measure state)
    (state next : γ) (h : target state = .inl next) : measure (θ next) < measure (θ state) := by
  have hc := commute (θ state)
  rw [right, h] at hc
  cases hs : step (θ state) with
  | inr value => simp [hs] at hc
  | inl next' =>
    simp only [hs, Sum.map_inl, Sum.inl.injEq] at hc
    rw [hc, left]
    exact decreases _ _ hs

theorem fixed_transport {step : α → Sum α β} {target : γ → Sum γ δ}
    (φ : α → γ) (θ : γ → α) (ψ : β → δ)
    (left : ∀ state, θ (φ state) = state) (right : ∀ state, φ (θ state) = state)
    (commute : ∀ state, target (φ state) = Sum.map φ ψ (step state))
    (meaning : α → β) (fixed : ∀ state, meaning state = (step state).elim meaning id)
    (state : γ) :
    ψ (meaning (θ state)) = (target state).elim (fun next => ψ (meaning (θ next))) id := by
  have hc := commute (θ state)
  rw [right] at hc
  rw [hc, fixed (θ state)]
  cases step (θ state) <;> simp [left]

theorem costAt_transport {step : α → Sum α β} {target : γ → Sum γ δ}
    (φ : α → γ) (ψ : β → δ)
    (commute : ∀ state, target (φ state) = Sum.map φ ψ (step state))
    (charge : α → Nat) (targetCharge : γ → Nat)
    (cost : ∀ state, targetCharge (φ state) = charge state) (fuel : Nat) (state : α) :
    costAt target targetCharge fuel (φ state) = costAt step charge fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [costAt, cost, commute]
    cases step state <;> simp [ih]

theorem fitsAt_transport {step : α → Sum α β} {target : γ → Sum γ δ}
    (φ : α → γ) (ψ : β → δ)
    (commute : ∀ state, target (φ state) = Sum.map φ ψ (step state))
    (valid : α → Bool) (targetValid : γ → Bool)
    (fits : ∀ state, targetValid (φ state) = valid state) (fuel : Nat) (state : α) :
    fitsAt target targetValid fuel (φ state) = fitsAt step valid fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [fitsAt, fits, commute]
    cases step state <;> simp [ih]

#print axioms decreases_transport
#print axioms withFixed_wellFounded
#print axioms withFixed_rank
#print axioms fixed_transport
#print axioms costAt_transport
#print axioms fitsAt_transport

end Verified.Tail
