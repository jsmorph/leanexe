import Examples.Euler.ReconstructedSpec
import Examples.Euler.Equations.Hyperbolicity

/-! The Euler flux is hyperbolic at the states of admissible cells.  For both solvers, the words
of a run that returns status 0 pack a final grid of such cells. -/

namespace Examples.Euler

open Examples.Euler

theorem Admissible.hyperbolic {c : Cell} (h : Admissible c) :
    Equations.Hyperbolic (vec c.state) :=
  Equations.admissible_hyperbolic _ h.2.2.2

/-- When the first word of `solve n` is 0, the words pack the final grid of a run, whose cells
are admissible and whose states are hyperbolic. -/
theorem solve_hyperbolic {n : UInt64} (h : (solve n)[0]! = 0) :
    ∃ time grid, solve n = pack n 0 time grid ∧
      ∀ c ∈ grid, Admissible c ∧ Equations.Hyperbolic (vec c.state) := by
  obtain ⟨status, time, grid, hRun⟩ : ∃ status time grid,
      Examples.Euler.run n = (status, time, grid) := ⟨_, _, _, rfl⟩
  have hSolve : solve n = pack n status time grid := by simp [solve, hRun]
  have hGrid : grid.size ≤ 640000 := by simpa [hRun] using run_size n
  have hStatus : status = 0 := by
    rw [hSolve, pack_word hGrid (by omega)] at h
    simpa using h
  subst hStatus
  have hAll := (run_ok (n := n) (by simp [hRun])).2.2.2.1
  simp only [hRun] at hAll
  exact ⟨time, grid, hSolve, fun c hc => ⟨hAll c hc, (hAll c hc).hyperbolic⟩⟩

/-- When the first word of `reconstructedSolve n trials` is 0, the words pack the final grid of
a run, whose cells are admissible and whose states are hyperbolic. -/
theorem reconstructedSolve_hyperbolic {n trials : UInt64}
    (h : (reconstructedSolve n trials)[0]! = 0) :
    ∃ time grid, reconstructedSolve n trials = pack n 0 time grid ∧
      ∀ c ∈ grid, Admissible c ∧ Equations.Hyperbolic (vec c.state) := by
  obtain ⟨status, time, grid, hRun⟩ : ∃ status time grid,
      reconstructedRun n trials = (status, time, grid) := ⟨_, _, _, rfl⟩
  have hSolve : reconstructedSolve n trials = pack n status time grid := by
    simp [reconstructedSolve, hRun]
  have hGrid : grid.size ≤ 640000 := by simpa [hRun] using reconstructedRun_size n trials
  have hStatus : status = 0 := by
    rw [hSolve, pack_word hGrid (by omega)] at h
    simpa using h
  subst hStatus
  have hAll := (reconstructedRun_ok (n := n) (trials := trials) (by simp [hRun])).2.2.2.1
  simp only [hRun] at hAll
  exact ⟨time, grid, hSolve, fun c hc => ⟨hAll c hc, (hAll c hc).hyperbolic⟩⟩

end Examples.Euler
