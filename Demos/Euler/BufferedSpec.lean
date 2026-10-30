import Demos.Euler.Buffered

/-! The buffered Euler solvers equal those of the first-order and reconstructed programs.  A sweep
into a grid of the right size equals the sweep that builds a new grid, by `loop_set`.  The loops
of tries and of timesteps map onto those of the programs under `first`, which keeps the status,
the time or timestep, and the first grid of a state, by `repeatWhile_map`, with the invariant that
the three grids have one size. -/

namespace Demos.Euler.Buffered

/-- A loop that writes `f i` at each index `i` below `k` into an array of `k` elements builds the
array of `f`. -/
theorem loop_set {α : Type} (k : UInt64) (out : Array α) (f : UInt64 → α)
    (h : out.size = k.toNat) :
    LeanExe.loop k out (fun i acc => acc.set! i.toNat (f i)) = LeanExe.build k f := by
  have key : ∀ j, j ≤ k.toNat → ∀ r : Array α,
      r = Nat.fold j (fun i _ acc => acc.set! (UInt64.ofNat i).toNat (f (UInt64.ofNat i))) out →
      r.size = k.toNat ∧ ∀ m (hm : m < j) (hr : m < r.size), r[m] = f (UInt64.ofNat m) := by
    intro j
    induction j with
    | zero =>
      intro _ r hr
      subst hr
      exact ⟨h, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
    | succ j ih =>
      intro hj r hr
      simp only [Nat.fold_succ] at hr
      obtain ⟨hs, he⟩ := ih (by omega) _ rfl
      generalize Nat.fold j (fun i _ acc => acc.set! (UInt64.ofNat i).toNat (f (UInt64.ofNat i)))
        out = r0 at hr hs he
      have hj' : (UInt64.ofNat j).toNat = j :=
        UInt64.toNat_ofNat_of_lt' (by have := k.toNat_lt; simp only [UInt64.size]; omega)
      subst hr
      simp only [hj', Array.set!_eq_setIfInBounds]
      refine ⟨by rw [Array.size_setIfInBounds, hs], fun m hm _ => ?_⟩
      have hm' : m < r0.size := by rw [hs]; omega
      rw [Array.getElem_setIfInBounds hm']
      split
      · subst_vars
        rfl
      · exact he m (by omega) hm'
  obtain ⟨hs, he⟩ := key k.toNat (Nat.le_refl _)
    (LeanExe.loop k out fun i acc => acc.set! i.toNat (f i)) rfl
  apply Array.ext
  · rw [hs]
    simp [LeanExe.build]
  · intro m h1 _
    rw [he m (by rw [hs] at h1; exact h1) h1]
    simp [LeanExe.build]

/-- A `LeanExe.repeatWhile` maps under `π` onto a second one when `π` carries the condition and
the step at every state of an invariant `P` that the step keeps. -/
theorem repeatWhile_map {α β : Type} (π : α → β) (P : α → Prop) {cond : α → Bool}
    {step : α → α} {cond' : β → Bool} {step' : β → β} (fuel : UInt64) (init : α) (h0 : P init)
    (hcond : ∀ s, P s → cond' (π s) = cond s)
    (hstep : ∀ s, P s → cond s = true → P (step s) ∧ π (step s) = step' (π s)) :
    P (LeanExe.repeatWhile fuel init cond step) ∧
      π (LeanExe.repeatWhile fuel init cond step) =
        LeanExe.repeatWhile fuel (π init) cond' step' := by
  unfold LeanExe.repeatWhile
  generalize fuel.toNat = k
  induction k generalizing init with
  | zero => exact ⟨h0, rfl⟩
  | succ k ih =>
    simp only [LeanExe.repeatWhile.go, hcond init h0]
    by_cases hc : cond init = true
    · obtain ⟨hP, hπ⟩ := hstep init h0 hc
      simp only [hc, ↓reduceIte, ← hπ]
      exact ih (step init) hP
    · simp only [hc]
      exact ⟨h0, rfl⟩

/-- The status, the time or timestep, and the first grid of a state of three grids. -/
abbrev first (s : UInt64 × Float × Array Cell × Array Cell × Array Cell) :
    UInt64 × Float × Array Cell :=
  (s.1, s.2.1, s.2.2.1)

/-- Each grid of a state of three grids has `c` cells. -/
abbrev Sized (c : Nat) (s : UInt64 × Float × Array Cell × Array Cell × Array Cell) : Prop :=
  s.2.2.1.size = c ∧ s.2.2.2.1.size = c ∧ s.2.2.2.2.size = c

private theorem size_sweep (n : UInt64) (axisY : Bool) (ratio : Float) (grid : Array Cell)
    (h : grid.size < 2 ^ 64) : (sweep n axisY ratio grid).size = grid.size := by
  simp [sweep, LeanExe.build, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' h]

private theorem size_reconstructedSweep (n : UInt64) (axisY : Bool) (trials : UInt64)
    (ratio : Float) (grid : Array Cell) (h : grid.size < 2 ^ 64) :
    (reconstructedSweep n axisY trials ratio grid).size = grid.size := by
  simp [reconstructedSweep, LeanExe.build, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' h]

private theorem size_initialCells (n : UInt64) : (initialCells n).size < 2 ^ 64 := by
  simp only [initialCells, LeanExe.build, Array.size_ofFn]
  exact (n * n).toNat_lt

theorem sweepInto_eq (n : UInt64) (axisY : Bool) (ratio : Float) (grid out : Array Cell)
    (h : out.size = grid.size) (hc : grid.size < 2 ^ 64) :
    sweepInto n axisY ratio grid out = sweep n axisY ratio grid := by
  unfold sweepInto sweep
  exact loop_set _ out _ (by rw [h]; simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hc])

theorem reconstructedSweepInto_eq (n : UInt64) (axisY : Bool) (trials : UInt64) (ratio : Float)
    (grid out : Array Cell) (h : out.size = grid.size) (hc : grid.size < 2 ^ 64) :
    reconstructedSweepInto n axisY trials ratio grid out =
      reconstructedSweep n axisY trials ratio grid := by
  unfold reconstructedSweepInto reconstructedSweep
  exact loop_set _ out _ (by rw [h]; simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hc])

theorem tryInto_eq (n : UInt64) (grid a b : Array Cell) (dt : Float) (hc : grid.size < 2 ^ 64)
    (ha : a.size = grid.size) (hb : b.size = grid.size) :
    Sized grid.size (tryInto n grid a b dt) ∧
      first (tryInto n grid a b dt) = tryStep n grid dt := by
  have s1 := size_sweep n false (dt / spacing n) grid hc
  have s2 := size_sweep n true (dt / spacing n) _ (s1 ▸ hc)
  unfold tryInto tryStep step finishStep
  simp only [sweepInto_eq n false _ grid a ha hc,
    sweepInto_eq n true _ _ b (hb.trans s1.symm) (s1 ▸ hc)]
  by_cases hx : accepted (sweep n false (dt / spacing n) grid) = true
  · by_cases hy : accepted (sweep n true (dt / spacing n) (sweep n false (dt / spacing n) grid))
        = true
    · simp [Sized, hx, hy, s1, s2]
    · simp [Sized, hx, hy, s1, s2]
  · simp [Sized, hx, s1, hb]

theorem attemptInto_eq (n : UInt64) (time dt : Float) (grid a b : Array Cell)
    (hc : grid.size < 2 ^ 64) (ha : a.size = grid.size) (hb : b.size = grid.size) :
    Sized grid.size (attemptInto n time dt grid a b) ∧
      first (attemptInto n time dt grid a b) = attempt n time dt grid := by
  unfold attemptInto attempt
  by_cases hv : validAdvance time dt = true
  · simp only [hv, ↓reduceIte]
    exact tryInto_eq n grid a b dt hc ha hb
  · simp only [hv]
    exact ⟨⟨rfl, ha, hb⟩, rfl⟩

theorem first_ite (c : Bool) (x y : UInt64 × Float × Array Cell × Array Cell × Array Cell) :
    first (if c then x else y) = if c then first x else first y := by
  cases c <;> rfl

theorem advanceInto_eq (n : UInt64) (time dt : Float) (grid a b : Array Cell)
    (hc : grid.size < 2 ^ 64) (ha : a.size = grid.size) (hb : b.size = grid.size) :
    Sized grid.size (advanceInto n time dt grid a b) ∧
      first (advanceInto n time dt grid a b) = advanceWith n time dt grid := by
  unfold advanceInto advanceWith
  generalize hR : LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid, a, b) _ _ = R
  generalize hR' : LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid) _ _ = R'
  have key : Sized grid.size R ∧ first R = R' := by
    rw [← hR, ← hR']
    refine repeatWhile_map first (Sized grid.size) 2048 _ ⟨rfl, ha, hb⟩ ?_ ?_
    · rintro ⟨_, _, _, _, _⟩ _
      rfl
    · rintro ⟨_, dt', g, a', b'⟩ ⟨hg, ha', hb'⟩ _
      dsimp only at hg ha' hb'
      have h := attemptInto_eq n time dt' g a' b' (by rw [hg]; exact hc) (ha'.trans hg.symm)
        (hb'.trans hg.symm)
      rw [hg] at h
      exact h
  obtain ⟨⟨hg, ha', hb'⟩, rfl⟩ := key
  obtain ⟨status, dt', g, a', b'⟩ := R
  dsimp only at hg ha' hb' ⊢
  refine ⟨?_, ?_⟩
  · split <;> exact ⟨hg, ha', hb'⟩
  · rw [first_ite]

theorem stepInto_eq (n status : UInt64) (time : Float) (grid a b : Array Cell)
    (hc : grid.size < 2 ^ 64) (ha : a.size = grid.size) (hb : b.size = grid.size) :
    Sized grid.size (stepInto n time grid a b) ∧
      first (stepInto n time grid a b) = advanceStep n status time grid := by
  unfold stepInto advanceStep
  by_cases hs : ((scan grid).1 == 0) = true
  · simp only [hs, ↓reduceIte]
    exact advanceInto_eq n time _ grid a b hc ha hb
  · simp only [hs]
    exact ⟨⟨rfl, ha, hb⟩, rfl⟩

theorem runFromInto_eq (n : UInt64) : first (runFromInto n) = runFrom n := by
  unfold runFromInto runFrom
  generalize hR : LeanExe.repeatWhile 4294967296
    ((0 : UInt64), (0 : Float), initialCells n, initialCells n, initialCells n) _ _ = R
  generalize hR' : LeanExe.repeatWhile 4294967296
    ((0 : UInt64), (0 : Float), initialCells n) _ _ = R'
  have key : Sized (initialCells n).size R ∧ first R = R' := by
    rw [← hR, ← hR']
    refine repeatWhile_map first (Sized (initialCells n).size) 4294967296 _ ⟨rfl, rfl, rfl⟩
      ?_ ?_
    · rintro ⟨_, _, _, _, _⟩ _
      rfl
    · rintro ⟨status, time, g, a', b'⟩ ⟨hg, ha', hb'⟩ _
      dsimp only at hg ha' hb'
      have h := stepInto_eq n status time g a' b' (by rw [hg]; exact size_initialCells n)
        (ha'.trans hg.symm) (hb'.trans hg.symm)
      rw [hg] at h
      exact h
  obtain ⟨-, rfl⟩ := key
  obtain ⟨status, time, g, a', b'⟩ := R
  dsimp only
  rw [first_ite]

theorem runInto_eq (n : UInt64) : runInto n = run n := by
  unfold runInto run
  by_cases hn : (2 ≤ n && n ≤ 800) = true
  · rw [ite_eq_left hn, ite_eq_left hn, ← runFromInto_eq n]
  · rw [ite_eq_right hn, ite_eq_right hn]

/-- The buffered first-order solver computes `Demos.Euler.solve`. -/
theorem solve_eq (n : UInt64) : Buffered.solve n = _root_.Demos.Euler.solve n := by
  unfold Buffered.solve _root_.Demos.Euler.solve
  rw [runInto_eq]

theorem reconstructedTryInto_eq (n trials : UInt64) (grid a b : Array Cell) (ratio dt : Float)
    (hc : grid.size < 2 ^ 64) (ha : a.size = grid.size) (hb : b.size = grid.size) :
    Sized grid.size (reconstructedTryInto n trials grid a b ratio dt) ∧
      first (reconstructedTryInto n trials grid a b ratio dt) =
        reconstructedTry n trials grid ratio dt := by
  have s1 := size_reconstructedSweep n false trials ratio grid hc
  have s2 := size_reconstructedSweep n true trials ratio _ (s1 ▸ hc)
  unfold reconstructedTryInto reconstructedTry reconstructedStepGrid reconstructedFinish
  simp only [reconstructedSweepInto_eq n false trials ratio grid a ha hc,
    reconstructedSweepInto_eq n true trials ratio _ b (hb.trans s1.symm) (s1 ▸ hc)]
  by_cases hx : accepted (reconstructedSweep n false trials ratio grid) = true
  · by_cases hy : accepted (reconstructedSweep n true trials ratio
        (reconstructedSweep n false trials ratio grid)) = true
    · simp [Sized, hx, hy, s1, s2]
    · simp [Sized, hx, hy, s1, s2]
  · simp [Sized, hx, s1, hb]

theorem reconstructedAttemptInto_eq (n trials : UInt64) (time alpha dt : Float)
    (grid a b : Array Cell) (hc : grid.size < 2 ^ 64) (ha : a.size = grid.size)
    (hb : b.size = grid.size) :
    Sized grid.size (reconstructedAttemptInto n trials time alpha dt grid a b) ∧
      first (reconstructedAttemptInto n trials time alpha dt grid a b) =
        reconstructedAttempt n trials time alpha dt grid := by
  unfold reconstructedAttemptInto reconstructedAttempt
  by_cases hv : validAdvance time dt = true
  · by_cases hr : ((gridRatio n dt alpha).status == 0) = true
    · simp only [hv, hr, ↓reduceIte]
      exact reconstructedTryInto_eq n trials grid a b _ dt hc ha hb
    · simp only [hv, hr, ↓reduceIte]
      exact ⟨⟨rfl, ha, hb⟩, rfl⟩
  · simp only [hv]
    exact ⟨⟨rfl, ha, hb⟩, rfl⟩

theorem reconstructedAdvanceInto_eq (n trials : UInt64) (time dt alpha : Float)
    (grid a b : Array Cell) (hc : grid.size < 2 ^ 64) (ha : a.size = grid.size)
    (hb : b.size = grid.size) :
    Sized grid.size (reconstructedAdvanceInto n trials time dt alpha grid a b) ∧
      first (reconstructedAdvanceInto n trials time dt alpha grid a b) =
        reconstructedAdvanceWith n trials time dt alpha grid := by
  unfold reconstructedAdvanceInto reconstructedAdvanceWith
  generalize hR : LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid, a, b) _ _ = R
  generalize hR' : LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid) _ _ = R'
  have key : Sized grid.size R ∧ first R = R' := by
    rw [← hR, ← hR']
    refine repeatWhile_map first (Sized grid.size) 2048 _ ⟨rfl, ha, hb⟩ ?_ ?_
    · rintro ⟨_, _, _, _, _⟩ _
      rfl
    · rintro ⟨_, dt', g, a', b'⟩ ⟨hg, ha', hb'⟩ _
      dsimp only at hg ha' hb'
      have h := reconstructedAttemptInto_eq n trials time alpha dt' g a' b' (by rw [hg]; exact hc)
        (ha'.trans hg.symm) (hb'.trans hg.symm)
      rw [hg] at h
      exact h
  obtain ⟨⟨hg, ha', hb'⟩, rfl⟩ := key
  obtain ⟨status, dt', g, a', b'⟩ := R
  dsimp only at hg ha' hb' ⊢
  refine ⟨?_, ?_⟩
  · split <;> exact ⟨hg, ha', hb'⟩
  · rw [first_ite]

theorem reconstructedStepInto_eq (n trials : UInt64) (time : Float) (grid a b : Array Cell)
    (hc : grid.size < 2 ^ 64) (ha : a.size = grid.size) (hb : b.size = grid.size) :
    Sized grid.size (reconstructedStepInto n trials time grid a b) ∧
      first (reconstructedStepInto n trials time grid a b) =
        reconstructedAdvanceStep n trials time grid := by
  unfold reconstructedStepInto reconstructedAdvanceStep
  by_cases hs : ((gridUpper grid).status == 0) = true
  · simp only [hs, ↓reduceIte]
    exact reconstructedAdvanceInto_eq n trials time _ _ grid a b hc ha hb
  · simp only [hs]
    exact ⟨⟨rfl, ha, hb⟩, rfl⟩

theorem reconstructedRunFromInto_eq (n trials : UInt64) :
    first (reconstructedRunFromInto n trials) = reconstructedRunFrom n trials := by
  unfold reconstructedRunFromInto reconstructedRunFrom
  generalize hR : LeanExe.repeatWhile 4294967296
    ((0 : UInt64), (0 : Float), initialCells n, initialCells n, initialCells n) _ _ = R
  generalize hR' : LeanExe.repeatWhile 4294967296
    ((0 : UInt64), (0 : Float), initialCells n) _ _ = R'
  have key : Sized (initialCells n).size R ∧ first R = R' := by
    rw [← hR, ← hR']
    refine repeatWhile_map first (Sized (initialCells n).size) 4294967296 _ ⟨rfl, rfl, rfl⟩
      ?_ ?_
    · rintro ⟨_, _, _, _, _⟩ _
      rfl
    · rintro ⟨_, time, g, a', b'⟩ ⟨hg, ha', hb'⟩ _
      dsimp only at hg ha' hb'
      have h := reconstructedStepInto_eq n trials time g a' b'
        (by rw [hg]; exact size_initialCells n) (ha'.trans hg.symm) (hb'.trans hg.symm)
      rw [hg] at h
      exact h
  obtain ⟨-, rfl⟩ := key
  obtain ⟨status, time, g, a', b'⟩ := R
  dsimp only
  rw [first_ite]

theorem reconstructedRunInto_eq (n trials : UInt64) :
    reconstructedRunInto n trials = reconstructedRun n trials := by
  unfold reconstructedRunInto reconstructedRun
  by_cases hn : (2 ≤ n && n ≤ 800) = true
  · rw [ite_eq_left hn, ite_eq_left hn, ← reconstructedRunFromInto_eq n trials]
  · rw [ite_eq_right hn, ite_eq_right hn]

/-- The buffered reconstructed solver computes `Demos.Euler.reconstructedSolve`. -/
theorem reconstructedSolve_eq (n trials : UInt64) :
    Buffered.reconstructedSolve n trials = _root_.Demos.Euler.reconstructedSolve n trials := by
  unfold Buffered.reconstructedSolve _root_.Demos.Euler.reconstructedSolve
  rw [reconstructedRunInto_eq]

#print axioms loop_set
#print axioms repeatWhile_map
#print axioms solve_eq
#print axioms reconstructedSolve_eq

end Demos.Euler.Buffered
