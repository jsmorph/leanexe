import LeanExe.Examples.EulerReconstructed
import Project.Euler.Spec

/-! Properties of the reconstructed Euler solver's Lean definitions. -/

namespace Project.Euler

open LeanExe.Examples.Euler

/-- `reconstructedAdvanceWith` with its loop's test and step named. -/
theorem reconstructedAdvanceWith_loop (n trials : UInt64) (time dt alpha : Float)
    (grid : Array Cell) :
    ∃ (cond : UInt64 × Float × Array Cell → Bool)
      (step : UInt64 × Float × Array Cell → UInt64 × Float × Array Cell),
      (∀ x, cond x = (x.1 == 9)) ∧
      (∀ x, step x = reconstructedAttempt n trials time alpha x.2.1 x.2.2) ∧
      reconstructedAdvanceWith n trials time dt alpha grid =
        match LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid) cond step with
        | (status, dt, g) =>
          if status == 0 then ((0 : UInt64), time + dt, g)
          else (if status == 9 then 4 else status, time, g) := by
  refine ⟨_, _, ?_, ?_, rfl⟩ <;> intro _ <;> rfl

/-- `reconstructedRunFrom` with its loop's test and step named. -/
theorem reconstructedRunFrom_loop (n trials : UInt64) :
    ∃ (cond : UInt64 × Float × Array Cell → Bool)
      (step : UInt64 × Float × Array Cell → UInt64 × Float × Array Cell),
      (∀ x, cond x = (x.1 == 0 && x.2.1.toBits != endTime.toBits)) ∧
      (∀ x, step x = reconstructedAdvanceStep n trials x.2.1 x.2.2) ∧
      reconstructedRunFrom n trials =
        match LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n) cond
          step with
        | (status, time, grid) =>
          if status == 0 && time.toBits != endTime.toBits then (5, time, grid)
          else (status, time, grid) := by
  refine ⟨_, _, ?_, ?_, rfl⟩ <;> intro _ <;> rfl

/-- A selection between a checked value and `rejectedChecked` with status 0 selects the value. -/
theorem rejectedChecked_status {c : Prop} [Decidable c] {u : Checked}
    (h : (if c then u else rejectedChecked).status = 0) : c := by
  by_cases hc : c
  · exact hc
  · rw [ite_eq_right hc] at h
    simp at h

theorem speedUpper_guard {rho mx my energy : Float}
    (h : (speedUpper rho mx my energy).status = 0) : stateGuard rho mx my energy = true := by
  unfold speedUpper at h
  dsimp only at h
  obtain ⟨h1, -⟩ := Bool.and_eq_true_iff.mp (rejectedChecked_status h)
  obtain ⟨h2, -⟩ := Bool.and_eq_true_iff.mp h1
  exact (Bool.and_eq_true_iff.mp h2).1

theorem outwardSide_guard {rho momentum transverse energy : Float}
    (h : (outwardSide rho momentum transverse energy).status = 0) :
    stateGuard rho momentum transverse energy = true := by
  unfold outwardSide at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact speedUpper_guard hc.1.1
  · simp at h

theorem faceStep_guard {ratio rho momentum transverse energy a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4
    d1 d2 d3 d4 : Float} {u : Updated}
    (hu : faceStep ratio rho momentum transverse energy a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2
      d3 d4 = u) (h : u.status = 0) :
    stateGuard u.density u.momentum u.transverse u.energy = true := by
  subst hu
  unfold faceStep at h ⊢
  dsimp only at h ⊢
  have hc := rejectedCell_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact outwardSide_guard hc.2

theorem reconstructedStep_guard {trials : UInt64} {ratio : Float} {a b c d e : Conserved}
    (h : (reconstructedStep trials ratio a b c d e).status = 0) :
    stateGuard (reconstructedStep trials ratio a b c d e).density
      (reconstructedStep trials ratio a b c d e).momentum
      (reconstructedStep trials ratio a b c d e).transverse
      (reconstructedStep trials ratio a b c d e).energy = true := by
  unfold reconstructedStep at h ⊢
  dsimp only at h ⊢
  have hc := rejectedCell_status h
  rw [ite_eq_left hc] at h ⊢
  exact faceStep_guard rfl h

/-- A state whose outward speed bound passes has positive density. -/
theorem speedUpper_ok {rho mx my energy : Float} (h : (speedUpper rho mx my energy).status = 0) :
    positive rho = true := by
  unfold speedUpper at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [stateGuard, narrowGuard, energyGuard, positive, Bool.and_eq_true,
      Bool.or_eq_true] at hc ⊢
    grind
  · simp at h

/-- A state that passes `outwardSide`'s checks has positive density and pressure. -/
theorem outwardSide_ok {rho momentum transverse energy : Float}
    (h : (outwardSide rho momentum transverse energy).status = 0) :
    positive rho = true ∧ positive (outwardSide rho momentum transverse energy).pressure = true := by
  unfold outwardSide at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i hc
    simp only [hc, ↓reduceIte]
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    refine ⟨speedUpper_ok hc.1.1, ?_⟩
    simp only [positive, Bool.and_eq_true] at hc ⊢
    grind
  · simp at h

theorem faceStep_ok {ratio rho momentum transverse energy a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4
    d1 d2 d3 d4 : Float}
    (h : (faceStep ratio rho momentum transverse energy a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2
      d3 d4).status = 0) :
    positive (faceStep ratio rho momentum transverse energy a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4
        d1 d2 d3 d4).density = true ∧
      positive (faceStep ratio rho momentum transverse energy a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4
        d1 d2 d3 d4).pressure = true := by
  unfold faceStep at h ⊢
  dsimp only at h ⊢
  have hc := rejectedCell_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact outwardSide_ok hc.2

theorem reconstructedStep_ok {trials : UInt64} {ratio : Float} {a b c d e : Conserved}
    (h : (reconstructedStep trials ratio a b c d e).status = 0) :
    positive (reconstructedStep trials ratio a b c d e).density = true ∧
      positive (reconstructedStep trials ratio a b c d e).pressure = true := by
  unfold reconstructedStep at h ⊢
  dsimp only at h ⊢
  have hc := rejectedCell_status h
  rw [ite_eq_left hc] at h ⊢
  exact faceStep_ok h

theorem reconstructedSweep_size (n : UInt64) (axisY : Bool) (trials : UInt64) (ratio : Float)
    (grid : Array Cell) (h : grid.size < 2 ^ 64) :
    (reconstructedSweep n axisY trials ratio grid).size = grid.size := by
  simp [reconstructedSweep, LeanExe.build, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' h]

/-- A cell of a reconstructed sweep with status 0 is admissible. -/
theorem reconstructedSweep_ok {n : UInt64} {axisY : Bool} {trials : UInt64} {ratio : Float}
    {grid : Array Cell} {c : Cell} (hc : c ∈ reconstructedSweep n axisY trials ratio grid)
    (h0 : c.status = 0) : Admissible c := by
  unfold reconstructedSweep LeanExe.build at hc
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hc
  dsimp only at h0 ⊢
  have ha := stateGuard_admissible (reconstructedStep_guard h0)
  refine ⟨h0, (reconstructedStep_ok h0).1, (reconstructedStep_ok h0).2, ?_⟩
  cases axisY
  · exact ha
  · exact admissible_swap ha

theorem reconstructedStepGrid_ok {n trials : UInt64} {ratio : Float} {grid : Array Cell}
    (h : accepted (reconstructedStepGrid n trials ratio grid) = true)
    (hSize : grid.size < 2 ^ 64) :
    (∀ c ∈ reconstructedStepGrid n trials ratio grid, Admissible c) ∧
      (reconstructedStepGrid n trials ratio grid).size = grid.size := by
  have hMiddle := reconstructedSweep_size n false trials ratio grid hSize
  unfold reconstructedStepGrid reconstructedFinish at h ⊢
  split
  · have hTrial := reconstructedSweep_size n true trials ratio
      (reconstructedSweep n false trials ratio grid) (by omega)
    rw [ite_eq_left (by assumption)] at h
    refine ⟨fun c hc => reconstructedSweep_ok hc (accepted_ok h (by omega) c hc), by omega⟩
  · rename_i hA
    rw [ite_eq_right hA] at h
    exact absurd h hA

theorem reconstructedStepGrid_size (n trials : UInt64) (ratio : Float) (grid : Array Cell)
    (hSize : grid.size < 2 ^ 64) :
    (reconstructedStepGrid n trials ratio grid).size = grid.size := by
  have hMiddle := reconstructedSweep_size n false trials ratio grid hSize
  unfold reconstructedStepGrid reconstructedFinish
  split
  · rw [reconstructedSweep_size n true trials ratio _ (by omega), hMiddle]
  · exact hMiddle

theorem reconstructedTry_ok {n trials : UInt64} {grid : Array Cell} {ratio dt : Float}
    (h : (reconstructedTry n trials grid ratio dt).1 = 0) (hSize : grid.size < 2 ^ 64) :
    (∀ c ∈ (reconstructedTry n trials grid ratio dt).2.2, Admissible c) ∧
      (reconstructedTry n trials grid ratio dt).2.2.size = grid.size := by
  unfold reconstructedTry at h ⊢
  dsimp only at h ⊢
  split
  · exact reconstructedStepGrid_ok (by assumption) hSize
  · rename_i hA
    rw [ite_eq_right hA] at h
    simp at h

theorem reconstructedTry_size (n trials : UInt64) (grid : Array Cell) (ratio dt : Float)
    (hSize : grid.size < 2 ^ 64) : (reconstructedTry n trials grid ratio dt).2.2.size = grid.size := by
  unfold reconstructedTry
  dsimp only
  split
  · exact reconstructedStepGrid_size n trials ratio grid hSize
  · rfl

theorem reconstructedAttempt_ok {n trials : UInt64} {time alpha dt : Float} {grid : Array Cell}
    (h : (reconstructedAttempt n trials time alpha dt grid).1 = 0)
    (hSize : grid.size < 2 ^ 64) :
    (∀ c ∈ (reconstructedAttempt n trials time alpha dt grid).2.2, Admissible c) ∧
      (reconstructedAttempt n trials time alpha dt grid).2.2.size = grid.size := by
  unfold reconstructedAttempt at h ⊢
  dsimp only at h ⊢
  split
  · rename_i hV
    rw [ite_eq_left hV] at h
    split
    · rename_i hR
      rw [ite_eq_left hR] at h
      exact reconstructedTry_ok h hSize
    · rename_i hR
      rw [ite_eq_right hR] at h
      simp at h
  · rename_i hV
    rw [ite_eq_right hV] at h
    simp at h

theorem reconstructedAttempt_size (n trials : UInt64) (time alpha dt : Float) (grid : Array Cell)
    (hSize : grid.size < 2 ^ 64) :
    (reconstructedAttempt n trials time alpha dt grid).2.2.size = grid.size := by
  unfold reconstructedAttempt
  dsimp only
  split
  · split
    · exact reconstructedTry_size n trials grid _ dt hSize
    · rfl
  · rfl

theorem reconstructedAdvanceWith_ok {n trials : UInt64} {time dt alpha : Float}
    {grid : Array Cell} (h : (reconstructedAdvanceWith n trials time dt alpha grid).1 = 0)
    (hSize : grid.size < 2 ^ 64) :
    (∀ c ∈ (reconstructedAdvanceWith n trials time dt alpha grid).2.2, Admissible c) ∧
      (reconstructedAdvanceWith n trials time dt alpha grid).2.2.size = grid.size := by
  obtain ⟨cond, step, -, hStepEq, hDef⟩ :=
    reconstructedAdvanceWith_loop n trials time dt alpha grid
  have hInv := repeatWhile_inv (P := fun s : UInt64 × Float × Array Cell =>
      s.2.2.size = grid.size ∧ (s.1 = 0 → ∀ c ∈ s.2.2, Admissible c)) (cond := cond)
    (step := step) (x0 := ((9 : UInt64), dt, grid)) 2048 ⟨rfl, by simp⟩
    (fun x _ hx => by
      rw [hStepEq]
      have hs := hx.1
      exact ⟨(reconstructedAttempt_size n trials time alpha x.2.1 x.2.2 (by omega)).trans hs,
        fun h0 => (reconstructedAttempt_ok h0 (by omega)).1⟩)
  rw [hDef] at h ⊢
  generalize LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid) cond step = R at h hInv ⊢
  obtain ⟨status, dt', g⟩ := R
  dsimp only at h hInv ⊢
  split
  · rename_i hS
    exact ⟨hInv.2 (by simpa using hS), hInv.1⟩
  · rename_i hS
    rw [ite_eq_right hS] at h
    split at h
    · simp at h
    · simp only at h
      exact absurd (by simp [h]) hS

theorem reconstructedAdvanceWith_size {n trials : UInt64} {time dt alpha : Float}
    {grid : Array Cell} (hSize : grid.size < 2 ^ 64) :
    (reconstructedAdvanceWith n trials time dt alpha grid).2.2.size = grid.size := by
  obtain ⟨cond, step, -, hStepEq, hDef⟩ :=
    reconstructedAdvanceWith_loop n trials time dt alpha grid
  have hInv := repeatWhile_inv (P := fun s : UInt64 × Float × Array Cell =>
      s.2.2.size = grid.size) (cond := cond) (step := step) (x0 := ((9 : UInt64), dt, grid)) 2048
    rfl (fun x _ hx => by
      rw [hStepEq]
      exact (reconstructedAttempt_size n trials time alpha x.2.1 x.2.2 (by omega)).trans hx)
  rw [hDef]
  generalize LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid) cond step = R at hInv ⊢
  obtain ⟨status, dt', g⟩ := R
  dsimp only at hInv ⊢
  split <;> exact hInv

theorem reconstructedAdvanceStep_ok {n trials : UInt64} {time : Float} {grid : Array Cell}
    (h : (reconstructedAdvanceStep n trials time grid).1 = 0) (hSize : grid.size < 2 ^ 64) :
    (∀ c ∈ (reconstructedAdvanceStep n trials time grid).2.2, Admissible c) ∧
      (reconstructedAdvanceStep n trials time grid).2.2.size = grid.size := by
  unfold reconstructedAdvanceStep at h ⊢
  dsimp only at h ⊢
  split
  · rename_i hS
    rw [ite_eq_left hS] at h
    exact reconstructedAdvanceWith_ok h hSize
  · rename_i hS
    rw [ite_eq_right hS] at h
    simp at h

theorem reconstructedAdvanceStep_size {n trials : UInt64} {time : Float} {grid : Array Cell}
    (hSize : grid.size < 2 ^ 64) :
    (reconstructedAdvanceStep n trials time grid).2.2.size = grid.size := by
  unfold reconstructedAdvanceStep
  dsimp only
  split
  · exact reconstructedAdvanceWith_size hSize
  · rfl

/-- A reconstructed run that returns status 0 reaches time 0.8 and ends with `n * n` admissible
cells. -/
theorem reconstructedRunFrom_ok {n trials : UInt64} (h : (reconstructedRunFrom n trials).1 = 0) :
    (reconstructedRunFrom n trials).2.1.toBits = endTime.toBits ∧
      (∀ c ∈ (reconstructedRunFrom n trials).2.2, Admissible c) ∧
      (reconstructedRunFrom n trials).2.2.size = (n * n).toNat := by
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ := reconstructedRunFrom_loop n trials
  have hN : (n * n).toNat < 2 ^ 64 := (n * n).toNat_lt
  have hInv := repeatWhile_inv (P := fun s : UInt64 × Float × Array Cell => s.1 = 0 →
      (s.2.1.toBits = 0 ∧ s.2.2 = initialCells n) ∨
        ((∀ c ∈ s.2.2, Admissible c) ∧ s.2.2.size = (n * n).toNat))
    (cond := cond) (step := step) (x0 := ((0 : UInt64), (0 : Float), initialCells n))
    4294967296 (fun _ => .inl ⟨zero_toBits, rfl⟩)
    (fun x hc hx hs => by
      rw [hStepEq] at hs ⊢
      have hc' : x.1 = 0 := by
        rw [hCondEq] at hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact hc.1
      have hSize : x.2.2.size = (n * n).toNat := by
        rcases hx hc' with ⟨-, h⟩ | ⟨-, h⟩
        · rw [h, initialCells_size]
        · exact h
      have := reconstructedAdvanceStep_ok hs (by omega)
      exact .inr ⟨this.1, this.2.trans hSize⟩)
  rw [hDef] at h ⊢
  generalize LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n) cond
    step = R at h hInv ⊢
  obtain ⟨status, time, grid⟩ := R
  dsimp only at h hInv ⊢
  split at h
  · simp at h
  · rename_i hT
    rw [ite_eq_right hT]
    subst h
    have hTime : time.toBits = endTime.toBits := by simpa using hT
    refine ⟨hTime, ?_⟩
    rcases hInv rfl with ⟨h0, -⟩ | hGood
    · rw [hTime] at h0
      exact absurd h0 (by decide +kernel)
    · exact hGood

theorem reconstructedRunFrom_size (n trials : UInt64) :
    (reconstructedRunFrom n trials).2.2.size = (n * n).toNat := by
  obtain ⟨cond, step, -, hStepEq, hDef⟩ := reconstructedRunFrom_loop n trials
  have hN : (n * n).toNat < 2 ^ 64 := (n * n).toNat_lt
  have hInv := repeatWhile_inv
    (P := fun s : UInt64 × Float × Array Cell => s.2.2.size = (n * n).toNat)
    (cond := cond) (step := step) (x0 := ((0 : UInt64), (0 : Float), initialCells n))
    4294967296 (initialCells_size n)
    (fun x _ hx => by rw [hStepEq, reconstructedAdvanceStep_size (by omega), hx])
  rw [hDef]
  generalize LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n) cond
    step = R at hInv ⊢
  obtain ⟨status, time, grid⟩ := R
  dsimp only at hInv ⊢
  split <;> exact hInv

theorem reconstructedRun_ok {n trials : UInt64} (h : (reconstructedRun n trials).1 = 0) :
    2 ≤ n ∧ n ≤ 800 ∧ (reconstructedRun n trials).2.1.toBits = endTime.toBits ∧
      (∀ c ∈ (reconstructedRun n trials).2.2, Admissible c) ∧
      (reconstructedRun n trials).2.2.size = (n * n).toNat := by
  unfold reconstructedRun at h ⊢
  split at h
  · rename_i hn
    rw [ite_eq_left hn]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
    exact ⟨hn.1, hn.2, reconstructedRunFrom_ok h⟩
  · simp at h

theorem reconstructedRun_size (n trials : UInt64) :
    (reconstructedRun n trials).2.2.size ≤ 640000 := by
  unfold reconstructedRun
  split
  · rename_i hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
    rw [reconstructedRunFrom_size, UInt64.toNat_mul]
    have h1 := UInt64.le_iff_toNat_le.mp hn.2
    have : n.toNat * n.toNat ≤ 800 * 800 := Nat.mul_le_mul (by simpa using h1) (by simpa using h1)
    simp only [UInt64.reduceToNat] at h1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · simp

/-- When the first word of `reconstructedSolve n trials` is 0, the words are those of a
successful run. -/
theorem reconstructedSolve_ok {n trials : UInt64} (h : (reconstructedSolve n trials)[0]! = 0) :
    Successful n (reconstructedSolve n trials) := by
  obtain ⟨status, time, grid, hRun⟩ : ∃ status time grid,
      reconstructedRun n trials = (status, time, grid) := ⟨_, _, _, rfl⟩
  have hSolve : reconstructedSolve n trials = pack n status time grid := by
    simp [reconstructedSolve, hRun]
  have hGrid : grid.size ≤ 640000 := by simpa [hRun] using reconstructedRun_size n trials
  rw [hSolve] at h ⊢
  rw [pack_word hGrid (by omega)] at h
  simp only [↓reduceIte] at h
  subst h
  obtain ⟨h2, h800, hTime, hAll, hSize⟩ := reconstructedRun_ok (n := n) (trials := trials)
    (by simp [hRun])
  simp only [hRun] at hTime hAll hSize
  refine ⟨h2, h800, by rw [pack_word hGrid (by omega)]; simpa using hTime, ?_, fun i hi => ?_⟩
  · rw [pack_size hGrid, hSize]
  · have hc := hAll grid[i]! (by rw [getElem!_pos grid i (by omega)]; exact Array.getElem_mem _)
    obtain ⟨-, hD, hP, -⟩ := hc
    simp only [positive, Bool.and_eq_true, decide_eq_true_eq] at hD hP
    rw [pack_word hGrid (by omega), pack_word hGrid (by omega)]
    rw [← hSize] at hi ⊢
    simp only [show ¬(4 + i = 0) by omega, show ¬(4 + i = 1) by omega, show ¬(4 + i < 4) by omega,
      show 4 + i < 4 + grid.size by omega, show ¬(4 + grid.size + i = 0) by omega,
      show ¬(4 + grid.size + i = 1) by omega, show ¬(4 + grid.size + i < 4) by omega,
      show ¬(4 + grid.size + i < 4 + grid.size) by omega, ↓reduceIte,
      show 4 + i - 4 = i by omega, show 4 + grid.size + i - 4 - grid.size = i by omega]
    exact ⟨hD, hP⟩

end Project.Euler
