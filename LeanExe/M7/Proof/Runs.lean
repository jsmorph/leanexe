import LeanExe.M7.Proof.Machine

/-!
Runs that never stop.  A step appends at most one device access to the trace (`step_trace`), so a
state that `Reach` gives lies `L` steps on for some `L` at least the growth of its trace
(`Reach.run_eq`), and `run` succeeds for every number of steps up to `L` (`run_le`).  A program
that reaches, for every `N`, a state whose trace has grown by `N` accesses therefore runs for every
number of steps without stopping the model (`runs_forever`).
-/

namespace LeanExe.M7

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-- The address of a device access. -/
def Access.addr : Access → UInt32
  | .read a _ => a
  | .write a _ => a

theorem State.trace_result (s : State) (sf : Fin 2) (d : Fin 8) (f : UInt32 × Bool × Bool) :
    (s.result sf d f).trace = s.trace := by
  unfold State.result
  split <;> rfl

theorem loadWord_trace {s u : State} {a v : UInt32} (h : loadWord P σ s a = some (v, u)) :
    u.trace.length ≤ s.trace.length + 1 := by
  unfold loadWord at h
  split at h
  · cases h
  · split at h
    · cases h
      simp
    · split at h
      · cases h
        omega
      · cases h

theorem storeWord_trace {s u : State} {a v : UInt32} (h : storeWord P s a v = some u) :
    u.trace.length ≤ s.trace.length + 1 := by
  unfold storeWord at h
  split at h
  · cases h
  · split at h
    · cases h
      simp
    · split at h
      · cases h
        simp
      · cases h

/-- An instruction appends at most one access to the trace. -/
theorem exec_trace {i : Instr} {s t : State} (h : exec P σ i s = some t) :
    t.trace.length ≤ s.trace.length + 1 := by
  cases i <;> simp only [exec] at h
  all_goals first
    | (obtain rfl := Option.some.inj h
       simp only [State.trace_result, State.setR, State.setNZCV]
       omega)
    | (obtain ⟨⟨v, u⟩, hu, rfl⟩ := Option.map_eq_some_iff.mp h
       have := loadWord_trace hu
       simp only [State.setR]
       omega)
    | (obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
       have := storeWord_trace hu
       simp only
       omega)
    | (split at h
       · cases h
       · obtain rfl := Option.some.inj h
         simp only [State.setR]
         omega)
    | (split at h
       · obtain rfl := Option.some.inj h
         simp only
         omega
       · cases h)

theorem step_trace {s t : State} (h : step P σ code s = some t) :
    t.trace.length ≤ s.trace.length + 1 := by
  simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, ⟨i, _⟩, -, he⟩ := h
  exact exec_trace he

/-- A state that zero or more steps reach lies `L` steps on, where `L` bounds the growth of the
trace. -/
theorem Reach.run_eq {s t : State} (h : Reach P σ code s t) :
    ∃ L, run P σ code L s = some t ∧ t.trace.length ≤ s.trace.length + L := by
  induction h with
  | refl s => exact ⟨0, rfl, by omega⟩
  | next hs _ ih =>
      obtain ⟨L, hL, hl⟩ := ih
      refine ⟨L + 1, by simp only [run, hs, Option.bind_some, hL], ?_⟩
      have := step_trace hs
      omega

/-- A run that succeeds for `L` steps succeeds for each smaller number. -/
theorem run_le {L : Nat} {s t : State} (h : run P σ code L s = some t) :
    ∀ k ≤ L, ∃ u, run P σ code k s = some u := by
  induction L generalizing s with
  | zero =>
      intro k hk
      exact ⟨s, by rw [show k = 0 by omega]; rfl⟩
  | succ L ih =>
      intro k hk
      cases k with
      | zero => exact ⟨s, rfl⟩
      | succ k =>
          simp only [run, Option.bind_eq_some_iff] at h
          obtain ⟨s', hs, hr⟩ := h
          obtain ⟨u, hu⟩ := ih hr k (by omega)
          exact ⟨u, by simp only [run, hs, Option.bind_some, hu]⟩

/-- A program that reaches, for every `N`, a state whose trace has `c + N` accesses runs for every
number of steps. -/
theorem runs_forever {b : State} {c : Nat}
    (h : ∀ N, ∃ s, Reach P σ code b s ∧ s.trace.length = c + N) :
    ∀ k, ∃ t, run P σ code k b = some t := by
  intro k
  obtain ⟨s, hr, hl⟩ := h (k + b.trace.length)
  obtain ⟨L, hL, hle⟩ := hr.run_eq
  exact run_le hL k (by omega)

end LeanExe.M7
