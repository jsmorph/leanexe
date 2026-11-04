import Demos.Energy.Gateway
import Demos.Energy.Words

/-! Theorems about the gateway of `Demos/Energy/Gateway.lean`.  Each concerns one tick, from a
state `g` and an input record `i`.  `tickClock g i` is the tick's clock, and `tickStart g i` the
state after the expiry check, from which the tick's other rules start.  `gateway_command` is G1
and G3: a tick outputs a command only when it accepts a snapshot whose words hold the tick's
clock and the recorded state, the command is the authorizer's decision, and the snapshot met the
gateway's conditions.  `gateway_fault` and `gateway_leaves` are G2: a faulty record, or
measurements outside the window in force, request fallback and end the window.
`gateway_record` is G4: the recorded state changes only by the expiry, a command, or a request to
return to fallback. -/

namespace Demos.Energy

/-- The state after the expiry check of a tick. -/
def tickStart (g : GwState) (i : GwIn) : GwState :=
  expire { g with seq := g.seq + 1, clock := tickClock g i, started := 1 } (tickClock g i)

/-- The snapshot that a tick would take. -/
def tickSnap (g : GwState) (i : GwIn) : Snap := snapOf (tickStart g i) i (tickClock g i)

theorem authorizeFlat_accepted {p : Prof} {s : Snap} (h : (authorizeFlat p s).status = .accepted) :
    (authorizeFlat p s).low = s.low ∧ (authorizeFlat p s).high = s.high ∧
      (authorizeFlat p s).expiry = s.time + p.window - p.tau := by
  unfold authorizeFlat at h ⊢
  simp only [] at h ⊢
  split_ifs at h ⊢ <;> simp_all [reject]

theorem siteProf_decision (s : Snap) : authorizeFlat siteProf s = authorizeWith site s.words := by
  rw [siteProf_eq, authorizeFlat_eq]

/-- The recorded state: the mode, the limits, a command's expiry, and the time of the last
change. -/
def GwState.record (g : GwState) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  (g.mode, g.low, g.high, g.expiry, g.changed)

/-- The cases of a tick, with the state and the output of each. -/
theorem gateway_cases (g : GwState) (i : GwIn) :
    (faulty g i = true ∧ gateway g i =
      (fallbackAt (tickStart g i) (tickClock g i), ⟨i.seq, 2, 0, 0, 0, g.status⟩)) ∨
    (faulty g i = false ∧ (leavesWindow (tickStart g i) i (tickClock g i) ||
      (!readBackOk (tickStart g i) i &&
        decide ((tickStart g i).changed + siteProf.tau ≤ tickClock g i))) = true ∧
      gateway g i =
        (fallbackAt (tickStart g i) (tickClock g i), ⟨i.seq, 2, 0, 0, 0, g.status⟩)) ∨
    (faulty g i = false ∧ leavesWindow (tickStart g i) i (tickClock g i) = false ∧
      readBackOk (tickStart g i) i = true ∧ powerIn siteProf (tickStart g i) i.power = true ∧
      (tickStart g i).changed + siteProf.tau ≤ tickClock g i ∧ i.proposal = 1 ∧
      (authorizeFlat siteProf (tickSnap g i)).status = .accepted ∧
      gateway g i = ({ tickStart g i with
          mode := 0, low := (authorizeFlat siteProf (tickSnap g i)).low,
          high := (authorizeFlat siteProf (tickSnap g i)).high,
          expiry := (authorizeFlat siteProf (tickSnap g i)).expiry, changed := tickClock g i,
          window := 1, windowEnd := tickClock g i + siteProf.window,
          bLow := lowBF siteProf (tickSnap g i), bHigh := highBF siteProf (tickSnap g i),
          loadLow := i.loadLow, loadHigh := i.loadHigh, pvLow := i.pvLow, pvHigh := i.pvHigh,
          status := 0 },
        ⟨i.seq, 1, (authorizeFlat siteProf (tickSnap g i)).low,
          (authorizeFlat siteProf (tickSnap g i)).high,
          (authorizeFlat siteProf (tickSnap g i)).expiry - tickClock g i, 0⟩)) ∨
    (faulty g i = false ∧ (gateway g i).2.kind = 0 ∧
      (gateway g i).1.record = (tickStart g i).record) := by
  unfold gateway gatewayWith
  simp only []
  split_ifs with h1 h2 h3 h4
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨by simpa using h1, h2, rfl⟩)
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at h2
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h3
    simp only [beq_iff_eq] at h4
    exact Or.inr (Or.inr (Or.inl ⟨by simpa using h1, h2.1, h3.1.1.2, h3.1.2, h3.2, h3.1.1.1,
      h4, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by simpa using h1, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by simpa using h1, rfl, rfl⟩))

/-- G1 and G3: a tick that outputs a command accepted the snapshot of its clock and recorded
state after the gateway's conditions held, and records the command, changed at the clock. -/
theorem gateway_command {g : GwState} {i : GwIn} (h : (gateway g i).2.kind = 1) :
    faulty g i = false ∧ leavesWindow (tickStart g i) i (tickClock g i) = false ∧
    readBackOk (tickStart g i) i = true ∧ powerIn siteProf (tickStart g i) i.power = true ∧
    (tickStart g i).changed + siteProf.tau ≤ tickClock g i ∧
    (authorizeWith site (tickSnap g i).words).status = .accepted ∧
    (gateway g i).2.low = i.low ∧ (gateway g i).2.high = i.high ∧
    (gateway g i).2.revert = (authorizeWith site (tickSnap g i).words).expiry - tickClock g i ∧
    (gateway g i).1.mode = 0 ∧ (gateway g i).1.low = i.low ∧ (gateway g i).1.high = i.high ∧
    (gateway g i).1.expiry = (authorizeWith site (tickSnap g i).words).expiry ∧
    (gateway g i).1.changed = tickClock g i := by
  rw [← siteProf_decision]
  rcases gateway_cases g i with
    ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨h1, h2, h3, h4, h5, -, h7, he⟩ | ⟨-, h0, -⟩
  · rw [he] at h
    simp at h
  · rw [he] at h
    simp at h
  · obtain ⟨hl, hh, -⟩ := authorizeFlat_accepted h7
    rw [he]
    exact ⟨h1, h2, h3, h4, h5, h7, hl, hh, rfl, rfl, hl, hh, rfl, rfl⟩
  · rw [h0] at h
    simp at h

/-- G2: a faulty record requests fallback, recorded at the tick's clock, and ends the window. -/
theorem gateway_fault {g : GwState} {i : GwIn} (h : faulty g i = true) :
    (gateway g i).2.kind = 2 ∧
      (gateway g i).1 = fallbackAt (tickStart g i) (tickClock g i) := by
  rcases gateway_cases g i with ⟨-, he⟩ | ⟨h1, -, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [he]
    exact ⟨rfl, rfl⟩
  all_goals simp [h] at h1

/-- G2: before the end of the window in force, measurements outside its intervals request
fallback, recorded at the tick's clock, and end the window. -/
theorem gateway_leaves {g : GwState} {i : GwIn} (hf : faulty g i = false)
    (h : leavesWindow (tickStart g i) i (tickClock g i) = true) :
    (gateway g i).2.kind = 2 ∧
      (gateway g i).1 = fallbackAt (tickStart g i) (tickClock g i) := by
  have he : gateway g i =
      (fallbackAt (tickStart g i) (tickClock g i), ⟨i.seq, 2, 0, 0, 0, g.status⟩) := by
    unfold gateway gatewayWith
    simp only []
    rw [ite_eq_right (by simp [hf]), ite_eq_left (by simp only [tickStart] at h; simp [h])]
    rfl
  rw [he]
  exact ⟨rfl, rfl⟩

/-- The expiry check changes the recorded state only to fallback at the expiry of a command
whose expiry is at most the clock. -/
theorem expire_record (g : GwState) (c : UInt64) :
    (expire g c).record = g.record ∨
      (g.mode = 0 ∧ g.expiry ≤ c ∧ (expire g c).record = (1, offset, offset, 0, g.expiry)) := by
  unfold expire
  split
  · rename_i hm
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
    exact Or.inr ⟨hm.1, hm.2, rfl⟩
  · exact Or.inl rfl

/-- G4: a tick changes the recorded state after the expiry check only by a command, recorded at
the tick's clock, or by a request to return to fallback, recorded at the tick's clock, and the
output's kind names the change. -/
theorem gateway_record (g : GwState) (i : GwIn) :
    ((gateway g i).2.kind = 0 ∧ (gateway g i).1.record = (tickStart g i).record) ∨
    ((gateway g i).2.kind = 1 ∧ (gateway g i).1.record = (0, i.low, i.high,
      (authorizeWith site (tickSnap g i).words).expiry, tickClock g i)) ∨
    ((gateway g i).2.kind = 2 ∧
      (gateway g i).1.record = (1, offset, offset, 0, tickClock g i)) := by
  rcases gateway_cases g i with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, -, -, -, -, h7, he⟩ | ⟨-, h⟩
  · rw [he]
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rw [he]
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · obtain ⟨hl, hh, -⟩ := authorizeFlat_accepted h7
    rw [he, ← siteProf_decision]
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    show (0, _, _, _, tickClock g i) = _
    rw [hl, hh]
    rfl
  · exact Or.inl h

end Demos.Energy
