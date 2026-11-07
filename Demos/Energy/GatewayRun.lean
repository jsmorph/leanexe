import Demos.Energy.GatewayTheorems
import Demos.Energy.Operation

/-! `OperatesIn.states` from the gateway's theorems and the device assumption.  A run of the
gateway reads the input records `ins`, from `gw0`.  Its recorded state changes at most twice a
tick: slot `2n` is the expiry of tick `n`, and slot `2n + 1` its command or its request to return
to fallback, each with the state that it records and its time on the gateway's clock.  `Follows`
is assumption A7 of the plan over these changes: once a change has had `τ` to take effect, the
device applies at each time `w` the state of a change whose time is at most `w`, and no change
older than every change whose time is at most `w - τ`.  `gateway_states` states
`OperatesIn.states` for every window of the run of the accepted snapshots up to a time `t`. -/

namespace Demos.Energy

open Spec Words

/-! ## Facts about one tick -/

/-- The device state of the recorded state. -/
def GwState.state (g : GwState) : State :=
  if g.mode = 1 then .fallback else .command ⟨signed g.low, signed g.high⟩

theorem state_of_record {g g' : GwState} (h : g.record = g'.record) : g.state = g'.state := by
  simp only [GwState.record, Prod.mk.injEq] at h
  simp only [GwState.state, h.1, h.2.1, h.2.2.1]

theorem expire_clock (g : GwState) (c : UInt64) : (expire g c).clock = g.clock := by
  unfold expire
  split <;> rfl

theorem gateway_clock (g : GwState) (i : GwIn) : (gateway g i).1.clock = tickClock g i := by
  unfold gateway gatewayWith
  simp only []
  split_ifs <;> simp [fallbackAt, expire_clock]

theorem clock_le_tickClock (g : GwState) (i : GwIn) : g.clock.toNat ≤ (tickClock g i).toNat := by
  unfold tickClock
  split
  · exact le_refl _
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h
    exact Nat.le_of_not_lt fun hh => h.1 (UInt64.lt_iff_toNat_lt.mpr hh)

theorem tickClock_lt {g : GwState} (h : g.clock.toNat < 1099511627776) (i : GwIn) :
    (tickClock g i).toNat < 1099511627776 := by
  unfold tickClock
  split
  · exact h
  · rename_i h'
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h'
    show _ < timeBound.toNat
    exact Nat.lt_of_not_le fun hh => h'.2 (UInt64.le_iff_toNat_le.mpr hh)

/-- After the expiry check, the last change lies at or before the clock. -/
theorem tickStart_changed {g : GwState} (h : g.changed.toNat ≤ g.clock.toNat) (i : GwIn) :
    (tickStart g i).changed.toNat ≤ (tickClock g i).toNat := by
  rcases expire_record { g with seq := g.seq + 1, clock := tickClock g i, started := 1 }
    (tickClock g i) with he | ⟨-, hx, he⟩
  · have : (tickStart g i).changed = g.changed := congrArg (·.2.2.2.2) he
    rw [this]
    exact h.trans (clock_le_tickClock g i)
  · have : (tickStart g i).changed = g.expiry := congrArg (·.2.2.2.2) he
    rw [this]
    exact UInt64.le_iff_toNat_le.mp hx

theorem gateway_changed {g : GwState} (h : g.changed.toNat ≤ g.clock.toNat) (i : GwIn) :
    (gateway g i).1.changed.toNat ≤ (gateway g i).1.clock.toNat := by
  rw [gateway_clock]
  rcases gateway_record g i with ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩
  · rw [show (gateway g i).1.changed = (tickStart g i).changed from congrArg (·.2.2.2.2) he]
    exact tickStart_changed h i
  · rw [show (gateway g i).1.changed = tickClock g i from congrArg (·.2.2.2.2) he]
  · rw [show (gateway g i).1.changed = tickClock g i from congrArg (·.2.2.2.2) he]

/-! ## Runs -/

variable (ins : ℕ → GwIn)

/-- The gateway's state before tick `n`. -/
def gwState : ℕ → GwState
  | 0 => gw0
  | n + 1 => (gateway (gwState n) (ins n)).1

/-- The kind of the output of tick `n`. -/
def gwKind (n : ℕ) : UInt64 := (gateway (gwState ins n) (ins n)).2.kind

/-- The clock of tick `n`. -/
def clk (n : ℕ) : ℕ := (tickClock (gwState ins n) (ins n)).toNat

/-- The change of the recorded state in slot `m`: the expiry of tick `m / 2` when `m` is even,
and its command or request to return to fallback when `m` is odd, with its state and time. -/
def change (m : ℕ) : Option (State × ℕ) :=
  if m % 2 = 0 then
    if (gwState ins (m / 2)).mode = 0 ∧
        (gwState ins (m / 2)).expiry ≤ tickClock (gwState ins (m / 2)) (ins (m / 2)) then
      some (.fallback, (gwState ins (m / 2)).expiry.toNat)
    else none
  else if gwKind ins (m / 2) = 0 then none
  else some ((gwState ins (m / 2 + 1)).state, clk ins (m / 2))

/-- Assumption A7 over the changes of the run, with `τ = 30` s: once some change has had `τ` to
take effect, the device applies at time `w` the state of a change whose time is at most `w`, and
whose slot is at or after that of every change whose time is at most `w - τ`. -/
def Follows (applied : ℝ → State) : Prop :=
  ∀ w : ℝ, (∃ m s t, change ins m = some (s, t) ∧ (t : ℝ) ≤ w - 30) →
    ∃ m s t, change ins m = some (s, t) ∧ (t : ℝ) ≤ w ∧ applied w = s ∧
      ∀ m' s' t', change ins m' = some (s', t') → (t' : ℝ) ≤ w - 30 → m' ≤ m

theorem change_even (n : ℕ) : change ins (2 * n) =
    if (gwState ins n).mode = 0 ∧ (gwState ins n).expiry ≤ tickClock (gwState ins n) (ins n)
    then some (.fallback, (gwState ins n).expiry.toNat) else none := by
  unfold change
  rw [if_pos (by omega), show 2 * n / 2 = n by omega]

theorem change_odd (n : ℕ) : change ins (2 * n + 1) =
    if gwKind ins n = 0 then none else some ((gwState ins (n + 1)).state, clk ins n) := by
  unfold change
  rw [if_neg (by omega), show (2 * n + 1) / 2 = n by omega]

theorem gwState_clock_lt : ∀ n, (gwState ins n).clock.toNat < 1099511627776
  | 0 => by show gw0.clock.toNat < 1099511627776; decide
  | n + 1 => by
      show (gateway (gwState ins n) (ins n)).1.clock.toNat < _
      rw [gateway_clock]
      exact tickClock_lt (gwState_clock_lt n) _

theorem gwState_changed : ∀ n, (gwState ins n).changed.toNat ≤ (gwState ins n).clock.toNat
  | 0 => by show gw0.changed.toNat ≤ gw0.clock.toNat; decide
  | n + 1 => gateway_changed (gwState_changed n) _

theorem clk_succ (n : ℕ) : clk ins n ≤ clk ins (n + 1) := by
  show _ ≤ (tickClock (gateway (gwState ins n) (ins n)).1 (ins (n + 1))).toNat
  have := clock_le_tickClock (gateway (gwState ins n) (ins n)).1 (ins (n + 1))
  rw [gateway_clock] at this
  exact this

theorem clk_mono {n n' : ℕ} (h : n ≤ n') : clk ins n ≤ clk ins n' := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact ih.trans (clk_succ ins _)

/-- The state before the expiry check of a tick. -/
def tickPre (g : GwState) (i : GwIn) : GwState :=
  { g with seq := g.seq + 1, clock := tickClock g i, started := 1 }

theorem tickStart_eq (g : GwState) (i : GwIn) :
    tickStart g i = expire (tickPre g i) (tickClock g i) := rfl

/-- Tick 0 requests fallback, since the gateway has not started. -/
theorem gwKind_zero : gwKind ins 0 = 2 :=
  (gateway_fault (by simp [faulty, gwState, gw0])).1

theorem expire_fires {g : GwState} {c : UInt64} (hm : g.mode = 0) (hx : g.expiry ≤ c) :
    (expire g c).mode = 1 := by
  unfold expire
  rw [ite_eq_left (by simp [hm, hx])]

/-- From the last change before tick `n`, the last change after the expiry check of tick `n`. -/
theorem last_change_start (n : ℕ) (h : ∃ mp, mp < 2 * n ∧
    change ins mp = some ((gwState ins n).state, (gwState ins n).changed.toNat) ∧
    ∀ m', mp < m' → m' < 2 * n → change ins m' = none) : ∃ mp, mp ≤ 2 * n ∧
    change ins mp = some ((tickStart (gwState ins n) (ins n)).state,
      (tickStart (gwState ins n) (ins n)).changed.toNat) ∧
    ∀ m', mp < m' → m' ≤ 2 * n → change ins m' = none := by
  rcases expire_record (tickPre (gwState ins n) (ins n)) (tickClock (gwState ins n) (ins n)) with
    he | ⟨hm, hx, he⟩
  · have he' : (tickStart (gwState ins n) (ins n)).record = (gwState ins n).record := he
    obtain ⟨mp, hlt, hc, hnone⟩ := h
    refine ⟨mp, by omega, ?_, fun m' h1 h2 => ?_⟩
    · rw [hc, state_of_record he', show (tickStart (gwState ins n) (ins n)).changed =
        (gwState ins n).changed from congrArg (·.2.2.2.2) he']
    · rcases Nat.lt_or_ge m' (2 * n) with h3 | h3
      · exact hnone m' h1 h3
      · rw [show m' = 2 * n by omega, change_even, ite_eq_right]
        rintro ⟨h4, h5⟩
        have h6 := expire_fires (g := tickPre (gwState ins n) (ins n)) h4 h5
        have h7 : (tickStart (gwState ins n) (ins n)).mode = (gwState ins n).mode :=
          congrArg (·.1) he'
        rw [tickStart_eq, h6, h4] at h7
        exact absurd h7 (by decide)
  · have hs : (tickStart (gwState ins n) (ins n)).record =
        (1, offset, offset, 0, (gwState ins n).expiry) := he
    refine ⟨2 * n, le_refl _, ?_, fun m' h1 h2 => absurd h2 (by omega)⟩
    rw [change_even, ite_eq_left ⟨hm, hx⟩]
    have hmode : (tickStart (gwState ins n) (ins n)).mode = 1 := congrArg (·.1) hs
    have hch : (tickStart (gwState ins n) (ins n)).changed = (gwState ins n).expiry :=
      congrArg (·.2.2.2.2) hs
    simp [GwState.state, hmode, hch]

/-- Before tick `n ≥ 1`, the last change in the slots before `2n` records the state and the time
of the gateway's recorded state. -/
theorem last_change : ∀ n, 1 ≤ n → ∃ mp, mp < 2 * n ∧
    change ins mp = some ((gwState ins n).state, (gwState ins n).changed.toNat) ∧
    ∀ m', mp < m' → m' < 2 * n → change ins m' = none
  | 0, h => absurd h (by decide)
  | n + 1, _ => by
      by_cases hk : gwKind ins n = 0
      · have hn1 : 1 ≤ n := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0
            rw [gwKind_zero] at hk
            exact absurd hk (by decide)
          · exact h0
        rcases gateway_record (gwState ins n) (ins n) with ⟨-, he⟩ | ⟨h1, -⟩ | ⟨h2, -⟩
        · obtain ⟨mp, hlt, hc, hn⟩ := last_change_start ins n (last_change n hn1)
          refine ⟨mp, by omega, ?_, fun m' h1 h2 => ?_⟩
          · rw [hc]
            show _ = some ((gateway (gwState ins n) (ins n)).1.state,
              (gateway (gwState ins n) (ins n)).1.changed.toNat)
            rw [state_of_record he, show (gateway (gwState ins n) (ins n)).1.changed =
              (tickStart (gwState ins n) (ins n)).changed from congrArg (·.2.2.2.2) he]
          · rcases Nat.lt_or_ge m' (2 * n + 1) with h3 | h3
            · exact hn m' h1 (by omega)
            · rw [show m' = 2 * n + 1 by omega, change_odd, ite_eq_left hk]
        · exact absurd (h1.symm.trans hk) (by decide)
        · exact absurd (h2.symm.trans hk) (by decide)
      · refine ⟨2 * n + 1, by omega, ?_, fun m' h1 h2 => absurd h2 (by omega)⟩
        rw [change_odd, ite_eq_right hk]
        have hch : (gateway (gwState ins n) (ins n)).1.changed =
            tickClock (gwState ins n) (ins n) := by
          rcases gateway_record (gwState ins n) (ins n) with ⟨h0, -⟩ | ⟨-, he⟩ | ⟨-, he⟩
          · exact absurd h0 hk
          · exact congrArg (·.2.2.2.2) he
          · exact congrArg (·.2.2.2.2) he
        show some ((gwState ins (n + 1)).state, (tickClock (gwState ins n) (ins n)).toNat) =
          some ((gwState ins (n + 1)).state, (gateway (gwState ins n) (ins n)).1.changed.toNat)
        rw [hch]

/-! ## `OperatesIn.states` -/

/-- From the time of an accepted snapshot at tick `a` until the clock of the next tick that
accepts one, the device applies the state that the snapshot records, the command of tick `a`, or
fallback. -/
theorem states_between (applied : ℝ → State) (hdev : Follows ins applied) {a : ℕ}
    (ha : gwKind ins a = 1) (w : ℝ) (hw : (clk ins a : ℝ) ≤ w)
    (hnext : ∀ b, a < b → gwKind ins b = 1 → w < clk ins b) :
    applied w = (tickStart (gwState ins a) (ins a)).state ∨
      applied w = .command ⟨signed (ins a).low, signed (ins a).high⟩ ∨
      applied w = .fallback := by
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0
      rw [gwKind_zero] at ha
      exact absurd ha (by decide)
    · exact h0
  obtain ⟨-, -, -, -, h5, -, -, -, -, hmode, hlow, hhigh, -, -⟩ := gateway_command ha
  have hle := tickStart_changed (gwState_changed ins a) (ins a)
  have hlt := tickClock_lt (gwState_clock_lt ins a) (ins a)
  have hc : (tickStart (gwState ins a) (ins a)).changed.toNat + 30 ≤ clk ins a := by
    have h := UInt64.le_iff_toNat_le.mp h5
    rw [UInt64.toNat_add, show siteProf.tau.toNat = 30 from rfl] at h
    unfold clk
    omega
  obtain ⟨mp, hmp, hcmp, hnone⟩ := last_change_start ins a (last_change ins a ha1)
  have hold : ((tickStart (gwState ins a) (ins a)).changed.toNat : ℝ) ≤ w - 30 := by
    have : ((tickStart (gwState ins a) (ins a)).changed.toNat : ℝ) + 30 ≤ clk ins a := by
      exact_mod_cast hc
    linarith
  obtain ⟨m, st, t, hm, htw, happ, hmax⟩ := hdev w ⟨mp, _, _, hcmp, hold⟩
  have hge : mp ≤ m := hmax mp _ _ hcmp hold
  rw [happ]
  rcases Nat.lt_or_ge m (2 * a + 1) with h1 | h1
  · rcases Nat.eq_or_lt_of_le hge with h2 | h2
    · subst h2
      rw [hcmp] at hm
      exact Or.inl (Prod.mk.inj (Option.some.inj hm)).1.symm
    · rw [hnone m h2 (by omega)] at hm
      cases hm
  · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · subst h2
      rw [change_odd, ite_eq_right (by rw [ha]; decide)] at hm
      have hst := (Prod.mk.inj (Option.some.inj hm)).1
      refine Or.inr (Or.inl ?_)
      rw [← hst]
      show (gateway (gwState ins a) (ins a)).1.state = _
      simp [GwState.state, hmode, hlow, hhigh]
    · rcases Nat.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
      · rw [show m = 2 * n by omega, change_even] at hm
        split at hm
        · exact Or.inr (Or.inr (Prod.mk.inj (Option.some.inj hm)).1.symm)
        · cases hm
      · rw [hn, change_odd] at hm
        split at hm
        · cases hm
        · rename_i hk
          have hpair := Prod.mk.inj (Option.some.inj hm)
          rcases gateway_record (gwState ins n) (ins n) with ⟨h0, -⟩ | ⟨h3, -⟩ | ⟨-, he⟩
          · exact absurd h0 hk
          · have := hnext n (by omega) h3
            have ht : (t : ℝ) = clk ins n := by exact_mod_cast hpair.2.symm
            linarith
          · refine Or.inr (Or.inr ?_)
            rw [← hpair.1]
            show (gateway (gwState ins n) (ins n)).1.state = _
            have hmode' : (gateway (gwState ins n) (ins n)).1.mode = 1 := congrArg (·.1) he
            simp [GwState.state, hmode']

/-- The snapshot words of tick `n`. -/
def snapWords (n : ℕ) : Array UInt64 := (tickSnap (gwState ins n) (ins n)).words

/-- `OperatesIn.states` for the run of the accepted snapshots `acc 0`, ..., `acc (J - 1)`, which
include every accepted snapshot up to the time `t`: in each window, until the next accepted
snapshot, the device applies the state that the snapshot records, the command authorized from
it, or fallback. -/
theorem gateway_states (applied : ℝ → State) (hdev : Follows ins applied) (J : ℕ)
    (acc : ℕ → ℕ) (hacc : StrictMono acc) (hkind : ∀ j < J, gwKind ins (acc j) = 1) (t : ℝ)
    (hall : ∀ b, gwKind ins b = 1 → (clk ins b : ℝ) ≤ t → ∃ j < J, acc j = b) (j : ℕ)
    (hj : j < J) : ∀ w ∈ Set.Icc ((runOf J fun j => snapWords ins (acc j)).time j) t,
      (runOf J fun j => snapWords ins (acc j)).Between j w →
      applied w = ((runOf J fun j => snapWords ins (acc j)).snapshot j).state ∨
      applied w = .command ((runOf J fun j => snapWords ins (acc j)).limits j) ∨
      applied w = .fallback := by
  intro w ⟨hw1, hw2⟩ hb
  have htime : (runOf J fun j => snapWords ins (acc j)).time j = clk ins (acc j) := rfl
  rw [htime] at hw1
  have hnext : ∀ b, acc j < b → gwKind ins b = 1 → w < clk ins b := by
    intro b hab hk
    by_contra hnot
    push_neg at hnot
    obtain ⟨j', hj', rfl⟩ := hall b hk (hnot.trans hw2)
    have hjj : j < j' := hacc.lt_iff_lt.mp hab
    have hb' := hb.2 (show j + 1 < J by omega)
    have : (runOf J fun j => snapWords ins (acc j)).time (j + 1) = clk ins (acc (j + 1)) := rfl
    rw [this] at hb'
    have hmono : clk ins (acc (j + 1)) ≤ clk ins (acc j') :=
      clk_mono ins (hacc.monotone (by omega))
    have : (clk ins (acc (j + 1)) : ℝ) ≤ clk ins (acc j') := by exact_mod_cast hmono
    linarith
  rcases states_between ins applied hdev (hkind j hj) w hw1 hnext with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end Demos.Energy
