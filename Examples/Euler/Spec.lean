import Examples.Euler.Program
import Examples.Euler.RealState

/-! Properties of the first-order Euler solver's Lean definitions.  A run that returns status 0
ends at time 0.8 with every cell admissible: status 0, density and pressure positive and finite,
and positive density and pressure in exact arithmetic. -/

namespace Examples.Euler

open Examples.Euler

/-- A cell that passed every check: status 0, positive and finite density and pressure, and a
state that is admissible in exact arithmetic. -/
def Admissible (c : Cell) : Prop :=
  c.status = 0 ∧ positive c.state.density = true ∧ positive c.pressure = true ∧
    Equations.Admissible (vec c.state)

/-- A state that passes `side`'s checks has positive density and positive pressure. -/
theorem side_ok {rho momentum transverse energy : Float}
    (h : (side rho momentum transverse energy).status = 0) :
    positive rho = true ∧ positive (side rho momentum transverse energy).pressure = true := by
  unfold side at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i hc
    simp only [hc, ↓reduceIte]
    simp only [stateGuard, narrowGuard, energyGuard, positive, Bool.and_eq_true,
      Bool.or_eq_true] at hc ⊢
    constructor <;> grind
  · simp at h

/-- A selection between an updated cell and `rejectedCell` with status 0 selects the cell. -/
theorem rejectedCell_status {c : Prop} [Decidable c] {u : Updated}
    (h : (if c then u else rejectedCell).status = 0) : c := by
  by_cases hc : c
  · exact hc
  · rw [ite_eq_right hc] at h
    simp at h

theorem advanceCell_ok {ratio rhoL momentumL transverseL energyL rho momentum transverse energy
    rhoR momentumR transverseR energyR : Float}
    (h : (advanceCell ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR
      momentumR transverseR energyR).status = 0) :
    positive (advanceCell ratio rhoL momentumL transverseL energyL rho momentum transverse energy
        rhoR momentumR transverseR energyR).density = true ∧
      positive (advanceCell ratio rhoL momentumL transverseL energyL rho momentum transverse energy
        rhoR momentumR transverseR energyR).pressure = true := by
  unfold advanceCell at h ⊢
  dsimp only at h ⊢
  have hc := rejectedCell_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact side_ok hc.2

theorem side_guard {rho momentum transverse energy : Float}
    (h : (side rho momentum transverse energy).status = 0) :
    stateGuard rho momentum transverse energy = true := by
  unfold side at h
  dsimp only at h
  split at h
  · rename_i hc
    obtain ⟨h1, -⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨h2, -⟩ := Bool.and_eq_true_iff.mp h1
    exact (Bool.and_eq_true_iff.mp h2).1
  · simp at h

theorem advanceCell_guard {ratio rhoL momentumL transverseL energyL rho momentum transverse energy
    rhoR momentumR transverseR energyR : Float} {u : Updated}
    (hu : advanceCell ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR
      momentumR transverseR energyR = u) (h : u.status = 0) :
    stateGuard u.density u.momentum u.transverse u.energy = true := by
  subst hu
  unfold advanceCell at h ⊢
  dsimp only at h ⊢
  have hc := rejectedCell_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact side_guard hc.2

theorem sweep_size (n : UInt64) (axisY : Bool) (ratio : Float) (grid : Array Cell)
    (h : grid.size < 2 ^ 64) : (sweep n axisY ratio grid).size = grid.size := by
  simp [sweep, LeanExe.build, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' h]

/-- A cell of a sweep with status 0 is admissible. -/
theorem sweep_ok {n : UInt64} {axisY : Bool} {ratio : Float} {grid : Array Cell} {c : Cell}
    (hc : c ∈ sweep n axisY ratio grid) (h0 : c.status = 0) : Admissible c := by
  unfold sweep LeanExe.build at hc
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hc
  dsimp only at h0 ⊢
  have ha := stateGuard_admissible (advanceCell_guard rfl h0)
  refine ⟨h0, (advanceCell_ok h0).1, (advanceCell_ok h0).2, ?_⟩
  cases axisY
  · exact ha
  · exact admissible_swap ha

theorem fold_and (k : Nat) (g : Nat → Bool) :
    Nat.fold k (fun i _ ok => ok && g i) true = true → ∀ i < k, g i = true := by
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro h i hi
    rw [Nat.fold_succ, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h.1 i hi
    · exact h.2

/-- Every cell of a grid that `accepted` passes has status 0. -/
theorem accepted_ok {grid : Array Cell} (h : accepted grid = true) (hSize : grid.size < 2 ^ 64) :
    ∀ c ∈ grid, c.status = 0 := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hc
  have hk : grid.size.toUInt64.toNat = grid.size := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hSize]
  have h' := fold_and grid.size.toUInt64.toNat
    (fun i => grid[(UInt64.ofNat i).toNat]!.status == 0) h i (by rw [hk]; exact hi)
  have hi' : (UInt64.ofNat i).toNat = i :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  simp only [hi', beq_iff_eq] at h'
  simpa [getElem!_pos grid i hi] using h'

/-- An accepted step's grid is admissible and keeps the grid's size. -/
theorem step_ok {n : UInt64} {ratio : Float} {grid : Array Cell}
    (h : accepted (step n ratio grid) = true) (hSize : grid.size < 2 ^ 64) :
    (∀ c ∈ step n ratio grid, Admissible c) ∧ (step n ratio grid).size = grid.size := by
  have hMiddle := sweep_size n false ratio grid hSize
  unfold step finishStep at h ⊢
  split
  · have hTrial := sweep_size n true ratio (sweep n false ratio grid) (by omega)
    rw [ite_eq_left (by assumption)] at h
    refine ⟨fun c hc => sweep_ok hc (accepted_ok h (by omega) c hc), by omega⟩
  · rename_i hA
    rw [ite_eq_right hA] at h
    exact absurd h hA

theorem step_size (n : UInt64) (ratio : Float) (grid : Array Cell) (hSize : grid.size < 2 ^ 64) :
    (step n ratio grid).size = grid.size := by
  have hMiddle := sweep_size n false ratio grid hSize
  unfold step finishStep
  split
  · rw [sweep_size n true ratio _ (by omega), hMiddle]
  · exact hMiddle

theorem tryStep_ok {n : UInt64} {grid : Array Cell} {dt : Float}
    (h : (tryStep n grid dt).1 = 0) (hSize : grid.size < 2 ^ 64) :
    (∀ c ∈ (tryStep n grid dt).2.2, Admissible c) ∧
      (tryStep n grid dt).2.2.size = grid.size := by
  unfold tryStep at h ⊢
  dsimp only at h ⊢
  split
  · exact step_ok (by assumption) hSize
  · rename_i hA
    rw [ite_eq_right hA] at h
    simp at h

theorem tryStep_size (n : UInt64) (grid : Array Cell) (dt : Float) (hSize : grid.size < 2 ^ 64) :
    (tryStep n grid dt).2.2.size = grid.size := by
  unfold tryStep
  dsimp only
  split
  · exact step_size n _ grid hSize
  · rfl

theorem attempt_ok {n : UInt64} {time dt : Float} {grid : Array Cell}
    (h : (attempt n time dt grid).1 = 0) (hSize : grid.size < 2 ^ 64) :
    (∀ c ∈ (attempt n time dt grid).2.2, Admissible c) ∧
      (attempt n time dt grid).2.2.size = grid.size := by
  unfold attempt at h ⊢
  split
  · rename_i hV
    rw [ite_eq_left hV] at h
    exact tryStep_ok h hSize
  · rename_i hV
    rw [ite_eq_right hV] at h
    simp at h

theorem attempt_size (n : UInt64) (time dt : Float) (grid : Array Cell)
    (hSize : grid.size < 2 ^ 64) : (attempt n time dt grid).2.2.size = grid.size := by
  unfold attempt
  split
  · exact tryStep_size n grid dt hSize
  · rfl

/-- A property that the start of a `LeanExe.repeatWhile` has and every step preserves holds at
its end. -/
theorem repeatWhile_inv {P : α → Prop} {cond : α → Bool} {step : α → α} {x0 : α} (fuel : UInt64)
    (h0 : P x0) (hStep : ∀ x, cond x = true → P x → P (step x)) :
    P (LeanExe.repeatWhile fuel x0 cond step) := by
  unfold LeanExe.repeatWhile
  generalize fuel.toNat = k
  induction k generalizing x0 with
  | zero => exact h0
  | succ k ih =>
    simp only [LeanExe.repeatWhile.go]
    split
    · exact ih (hStep x0 (by assumption) h0)
    · exact h0

/-- `advanceWith` with its loop's test and step named. -/
theorem advanceWith_loop (n : UInt64) (time dt : Float) (grid : Array Cell) :
    ∃ (cond : UInt64 × Float × Array Cell → Bool)
      (step : UInt64 × Float × Array Cell → UInt64 × Float × Array Cell),
      (∀ x, cond x = (x.1 == 9)) ∧ (∀ x, step x = attempt n time x.2.1 x.2.2) ∧
      advanceWith n time dt grid =
        match LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid) cond step with
        | (status, dt, g) =>
          if status == 0 then ((0 : UInt64), time + dt, g)
          else (if status == 9 then 4 else status, time, g) := by
  refine ⟨_, _, ?_, ?_, rfl⟩ <;> intro _ <;> rfl

/-- `runFrom` with its loop's test and step named. -/
theorem runFrom_loop (n : UInt64) :
    ∃ (cond : UInt64 × Float × Array Cell → Bool)
      (step : UInt64 × Float × Array Cell → UInt64 × Float × Array Cell),
      (∀ x, cond x = (x.1 == 0 && x.2.1.toBits != endTime.toBits)) ∧
      (∀ x, step x = advanceStep n x.1 x.2.1 x.2.2) ∧
      runFrom n =
        match LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n) cond
          step with
        | (status, time, grid) =>
          if status == 0 && time.toBits != endTime.toBits then (5, time, grid)
          else (status, time, grid) := by
  refine ⟨_, _, ?_, ?_, rfl⟩ <;> intro _ <;> rfl

theorem advanceWith_ok {n : UInt64} {time dt : Float} {grid : Array Cell}
    (h : (advanceWith n time dt grid).1 = 0) (hSize : grid.size < 2 ^ 64) :
    (∀ c ∈ (advanceWith n time dt grid).2.2, Admissible c) ∧
      (advanceWith n time dt grid).2.2.size = grid.size := by
  obtain ⟨cond, step, -, hStepEq, hDef⟩ := advanceWith_loop n time dt grid
  have hInv := repeatWhile_inv (P := fun s : UInt64 × Float × Array Cell =>
      s.2.2.size = grid.size ∧ (s.1 = 0 → ∀ c ∈ s.2.2, Admissible c)) (cond := cond)
    (step := step) (x0 := ((9 : UInt64), dt, grid)) 2048 ⟨rfl, by simp⟩
    (fun x _ hx => by
      rw [hStepEq]
      have hs := hx.1
      exact ⟨(attempt_size n time x.2.1 x.2.2 (by omega)).trans hs,
        fun h0 => (attempt_ok h0 (by omega)).1⟩)
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

theorem advanceStep_ok {n status : UInt64} {time : Float} {grid : Array Cell}
    (h : (advanceStep n status time grid).1 = 0) (hSize : grid.size < 2 ^ 64) :
    (∀ c ∈ (advanceStep n status time grid).2.2, Admissible c) ∧
      (advanceStep n status time grid).2.2.size = grid.size := by
  unfold advanceStep at h ⊢
  dsimp only at h ⊢
  split
  · rename_i hS
    rw [ite_eq_left hS] at h
    exact advanceWith_ok h hSize
  · rename_i hS
    rw [ite_eq_right hS] at h
    simp at h

theorem initialCells_size (n : UInt64) : (initialCells n).size = (n * n).toNat := by
  simp [initialCells, LeanExe.build]

/-- A run that returns status 0 reaches time 0.8 and ends with `n * n` admissible cells. -/
theorem runFrom_ok {n : UInt64} (h : (runFrom n).1 = 0) :
    (runFrom n).2.1.toBits = endTime.toBits ∧ (∀ c ∈ (runFrom n).2.2, Admissible c) ∧
      (runFrom n).2.2.size = (n * n).toNat := by
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ := runFrom_loop n
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
      have := advanceStep_ok hs (by omega)
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

theorem advanceWith_size {n : UInt64} {time dt : Float} {grid : Array Cell}
    (hSize : grid.size < 2 ^ 64) : (advanceWith n time dt grid).2.2.size = grid.size := by
  obtain ⟨cond, step, -, hStepEq, hDef⟩ := advanceWith_loop n time dt grid
  have hInv := repeatWhile_inv (P := fun s : UInt64 × Float × Array Cell =>
      s.2.2.size = grid.size) (cond := cond) (step := step) (x0 := ((9 : UInt64), dt, grid)) 2048
    rfl (fun x _ hx => by rw [hStepEq]; exact (attempt_size n time x.2.1 x.2.2 (by omega)).trans hx)
  rw [hDef]
  generalize LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid) cond step = R at hInv ⊢
  obtain ⟨status, dt', g⟩ := R
  dsimp only at hInv ⊢
  split <;> exact hInv

theorem advanceStep_size {n status : UInt64} {time : Float} {grid : Array Cell}
    (hSize : grid.size < 2 ^ 64) : (advanceStep n status time grid).2.2.size = grid.size := by
  unfold advanceStep
  dsimp only
  split
  · exact advanceWith_size hSize
  · rfl

theorem runFrom_size (n : UInt64) : (runFrom n).2.2.size = (n * n).toNat := by
  obtain ⟨cond, step, -, hStepEq, hDef⟩ := runFrom_loop n
  have hN : (n * n).toNat < 2 ^ 64 := (n * n).toNat_lt
  have hInv := repeatWhile_inv
    (P := fun s : UInt64 × Float × Array Cell => s.2.2.size = (n * n).toNat)
    (cond := cond) (step := step) (x0 := ((0 : UInt64), (0 : Float), initialCells n))
    4294967296 (initialCells_size n)
    (fun x _ hx => by rw [hStepEq, advanceStep_size (by omega), hx])
  rw [hDef]
  generalize LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n) cond
    step = R at hInv ⊢
  obtain ⟨status, time, grid⟩ := R
  dsimp only at hInv ⊢
  split <;> exact hInv

/-- A run with status 0 has a grid size from 2 to 800 and ends at time 0.8 with `n * n`
admissible cells. -/
theorem run_ok {n : UInt64} (h : (Examples.Euler.run n).1 = 0) :
    2 ≤ n ∧ n ≤ 800 ∧ (Examples.Euler.run n).2.1.toBits = endTime.toBits ∧
      (∀ c ∈ (Examples.Euler.run n).2.2, Admissible c) ∧
      (Examples.Euler.run n).2.2.size = (n * n).toNat := by
  unfold Examples.Euler.run at h ⊢
  split at h
  · rename_i hn
    rw [ite_eq_left hn]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
    exact ⟨hn.1, hn.2, runFrom_ok h⟩
  · simp at h

theorem run_size (n : UInt64) : (Examples.Euler.run n).2.2.size ≤ 640000 := by
  unfold Examples.Euler.run
  split
  · rename_i hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
    rw [runFrom_size, UInt64.toNat_mul]
    have h1 := UInt64.le_iff_toNat_le.mp hn.2
    have : n.toNat * n.toNat ≤ 800 * 800 := Nat.mul_le_mul (by simpa using h1) (by simpa using h1)
    simp only [UInt64.reduceToNat] at h1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · simp

theorem pack_size {n status : UInt64} {time : Float} {grid : Array Cell}
    (hGrid : grid.size ≤ 640000) : (pack n status time grid).size = 4 + 2 * grid.size := by
  have hk : grid.size.toUInt64.toNat = grid.size := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (show grid.size < 2 ^ 64 by omega)]
  simp [pack, LeanExe.build, UInt64.toNat_add, UInt64.toNat_mul, hk]
  omega

/-- Word `j` of `pack`, with the tests on words as tests on natural numbers. -/
theorem pack_word {n status : UInt64} {time : Float} {grid : Array Cell} {j : Nat}
    (hGrid : grid.size ≤ 640000) (hj : j < 4 + 2 * grid.size) :
    (pack n status time grid)[j]! =
      if j = 0 then status else if j = 1 then time.toBits else if j < 4 then n
      else if j < 4 + grid.size then grid[j - 4]!.state.density.toBits
      else grid[j - 4 - grid.size]!.pressure.toBits := by
  have hk : grid.size.toUInt64.toNat = grid.size := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (show grid.size < 2 ^ 64 by omega)]
  have hCount : (4 + 2 * grid.size.toUInt64).toNat = 4 + 2 * grid.size := by
    simp [UInt64.toNat_add, UInt64.toNat_mul, hk]
    omega
  have hJ : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  unfold pack
  simp only [LeanExe.build]
  rw [getElem!_pos _ j (by simp [hCount]; omega), Array.getElem_ofFn]
  simp only [beq_iff_eq, ← UInt64.toNat_inj, UInt64.lt_iff_toNat_lt, hJ, UInt64.toNat_add, hk,
    UInt64.reduceToNat]
  by_cases h0 : j = 0
  · simp [h0]
  by_cases h1 : j = 1
  · simp [h1]
  by_cases h4 : j < 4
  · simp [h0, h1, h4]
  have hSub : (UInt64.ofNat j - 4).toNat = j - 4 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp [hJ]; omega)), hJ]
    rfl
  by_cases hD : j < 4 + grid.size
  · simp [h0, h1, h4, Nat.mod_eq_of_lt (show 4 + grid.size < 18446744073709551616 by omega), hD, hSub]
  · have hSub2 : (UInt64.ofNat j - 4 - grid.size.toUInt64).toNat = j - 4 - grid.size := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hSub, hk]; omega)),
        hSub, hk]
    simp [h0, h1, h4, Nat.mod_eq_of_lt (show 4 + grid.size < 18446744073709551616 by omega), hD, hSub2]

/-- The words of a run that succeeds on an `n × n` grid: `n` lies from 2 to 800, the second word
holds the bits of 0.8, and after the four header words come `n * n` densities and then `n * n`
pressures, each positive and finite. -/
def Successful (n : UInt64) (words : Array UInt64) : Prop :=
  2 ≤ n ∧ n ≤ 800 ∧ words[1]! = endTime.toBits ∧ words.size = 4 + 2 * (n * n).toNat ∧
    ∀ i < (n * n).toNat,
      (0 < words[4 + i]! ∧ words[4 + i]! < 0x7FF0000000000000) ∧
      (0 < words[4 + (n * n).toNat + i]! ∧ words[4 + (n * n).toNat + i]! < 0x7FF0000000000000)

/-- When the first word of `solve n` is 0, the words are those of a successful run. -/
theorem solve_ok {n : UInt64} (h : (solve n)[0]! = 0) : Successful n (solve n) := by
  obtain ⟨status, time, grid, hRun⟩ : ∃ status time grid,
      Examples.Euler.run n = (status, time, grid) := ⟨_, _, _, rfl⟩
  have hSolve : solve n = pack n status time grid := by simp [solve, hRun]
  have hGrid : grid.size ≤ 640000 := by simpa [hRun] using run_size n
  rw [hSolve] at h ⊢
  rw [pack_word hGrid (by omega)] at h
  simp only [↓reduceIte] at h
  subst h
  obtain ⟨h2, h800, hTime, hAll, hSize⟩ := run_ok (n := n) (by simp [hRun])
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

end Examples.Euler
