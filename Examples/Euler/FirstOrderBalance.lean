import Examples.Euler.Balance
import Examples.Euler.Spec

/-! Conservation balance of the first-order solver: of a sweep, of an accepted step, and of a run
that returns status 0. -/

namespace Examples.Euler

open Examples.Euler LeanExe.ProofKit

/-- The Rusanov flux between two states. -/
def stateFlux (a b : Conserved) : Flux :=
  flux a.density a.mx a.my a.energy b.density b.mx b.my b.energy

/-- An accepted update of the center of three states updates each component with the fluxes at
its two faces. -/
theorem advanceCell_parts {ratio : Float} {a b d : Conserved}
    (h : (advanceCell ratio a.density a.mx a.my a.energy b.density b.mx b.my b.energy d.density
      d.mx d.my d.energy).status = 0) (c : Fin 4) :
    (update ratio (stateAt b c) (fluxAt (stateFlux a b) c) (fluxAt (stateFlux b d) c)).status = 0 ∧
      updatedAt (advanceCell ratio a.density a.mx a.my a.energy b.density b.mx b.my b.energy
        d.density d.mx d.my d.energy) c =
        (update ratio (stateAt b c) (fluxAt (stateFlux a b) c) (fluxAt (stateFlux b d) c)).value := by
  unfold advanceCell at h ⊢
  dsimp only at h ⊢
  have hc := rejectedCell_status h
  rw [ite_eq_left hc]
  obtain ⟨h1, -⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨-, hn⟩ := Bool.and_eq_true_iff.mp h1
  obtain ⟨hn3, he⟩ := Bool.and_eq_true_iff.mp hn
  obtain ⟨hn2, ht⟩ := Bool.and_eq_true_iff.mp hn3
  obtain ⟨hd, hm⟩ := Bool.and_eq_true_iff.mp hn2
  fin_cases c
  · exact ⟨beq_iff_eq.mp hd, rfl⟩
  · exact ⟨beq_iff_eq.mp hm, rfl⟩
  · exact ⟨beq_iff_eq.mp ht, rfl⟩
  · exact ⟨beq_iff_eq.mp he, rfl⟩

/-- The update of position `p` of line `l` from its two neighbors, clamped at the ends of the
line. -/
def firstLineStep (m : Nat) (axisY : Bool) (ratio : Float) (grid : Array Cell) (l p : Nat) :
    Updated :=
  advanceCell ratio (lineState m axisY grid l (p - 1)).density (lineState m axisY grid l (p - 1)).mx
    (lineState m axisY grid l (p - 1)).my (lineState m axisY grid l (p - 1)).energy
    (lineState m axisY grid l p).density (lineState m axisY grid l p).mx
    (lineState m axisY grid l p).my (lineState m axisY grid l p).energy
    (lineState m axisY grid l (min (p + 1) (m - 1))).density
    (lineState m axisY grid l (min (p + 1) (m - 1))).mx
    (lineState m axisY grid l (min (p + 1) (m - 1))).my
    (lineState m axisY grid l (min (p + 1) (m - 1))).energy

/-- The cell at index `k` of a sweep is the update of its position on its line. -/
theorem sweep_cell {n : UInt64} {axisY : Bool} {ratio : Float} {grid : Array Cell}
    (hsize : grid.size = n.toNat * n.toNat) (hlt : grid.size < 2 ^ 64) {k : Nat}
    (hk : k < grid.size) :
    (sweep n axisY ratio grid)[k]! = cellOf axisY (firstLineStep n.toNat axisY ratio grid
      (lineOf n.toNat axisY k) (positionOf n.toNat axisY k)) := by
  have hsz := sweep_size n axisY ratio grid hlt
  rw [getElem!_pos _ k (by omega)]
  unfold sweep LeanExe.build
  rw [Array.getElem_ofFn]
  dsimp only
  obtain ⟨hc', hs', hX, hB, hp⟩ := sweep_index (axisY := axisY) (k := k) (by rw [← hsize]; exact hk)
    (by rw [← hsize]; exact hlt)
  set m := n.toNat with hmdef
  generalize (if axisY = true then UInt64.ofNat k / n else UInt64.ofNat k % n) = c at hc' ⊢
  generalize (if axisY = true then n else 1) = stride at hs' ⊢
  obtain ⟨hL, -⟩ := step_down hX hc' hs'
  generalize (if c == 0 then UInt64.ofNat k else UInt64.ofNat k - stride) = lower at hL ⊢
  obtain ⟨hU, -⟩ := step_up hX hc' hs' hmdef.symm hp hB
  generalize (if c + 1 < n then UInt64.ofNat k + stride else UInt64.ofNat k) = upper at hU ⊢
  rw [hL, hU, hX]
  rfl

/-- The flux at face `j` of line `l`, between positions `j - 1` and `j`, clamped at the ends of
the line. -/
def firstLineFace (m : Nat) (axisY : Bool) (grid : Array Cell) (l j : Nat) : Flux :=
  stateFlux (lineState m axisY grid l (j - 1)) (lineState m axisY grid l (min j (m - 1)))

theorem firstLineStep_parts {m : Nat} {axisY : Bool} {ratio : Float} {grid : Array Cell}
    {l p : Nat} (hp : p < m) (h : (firstLineStep m axisY ratio grid l p).status = 0) (c : Fin 4) :
    (update ratio (stateAt (lineState m axisY grid l p) c)
        (fluxAt (firstLineFace m axisY grid l p) c)
        (fluxAt (firstLineFace m axisY grid l (p + 1)) c)).status = 0 ∧
      updatedAt (firstLineStep m axisY ratio grid l p) c =
        (update ratio (stateAt (lineState m axisY grid l p) c)
          (fluxAt (firstLineFace m axisY grid l p) c)
          (fluxAt (firstLineFace m axisY grid l (p + 1)) c)).value := by
  simp only [firstLineFace, show min p (m - 1) = p by omega, show p + 1 - 1 = p by omega]
  exact advanceCell_parts h c

theorem sweep_balance (n : UInt64) (axisY : Bool) (ratio : Float) (grid : Array Cell)
    (hsize : grid.size = n.toNat * n.toNat) (hlt : grid.size < 2 ^ 64) (c : Fin 4) :
    total (sweep n axisY ratio grid) c =
      total grid c - real ratio * boundary n.toNat axisY (firstLineFace n.toNat axisY grid) c +
        residual n.toNat axisY ratio (firstLineFace n.toNat axisY grid) grid
          (sweep n axisY ratio grid) c :=
  balance_identity hsize (sweep_size n axisY ratio grid hlt) c

theorem sweep_residual_le {n : UInt64} {axisY : Bool} {ratio : Float} {grid : Array Cell}
    (hsize : grid.size = n.toNat * n.toNat) (hlt : grid.size < 2 ^ 64)
    (hA : accepted (sweep n axisY ratio grid) = true) (c : Fin 4) :
    |residual n.toNat axisY ratio (firstLineFace n.toNat axisY grid) grid
        (sweep n axisY ratio grid) c| ≤
      residualBound n.toNat axisY ratio (firstLineFace n.toNat axisY grid) grid c := by
  have hsz := sweep_size n axisY ratio grid hlt
  refine residual_le (fun k hk c => ?_) c
  have hcell := sweep_cell (axisY := axisY) (ratio := ratio) hsize hlt hk
  have h0 : (firstLineStep n.toNat axisY ratio grid (lineOf n.toNat axisY k)
      (positionOf n.toNat axisY k)).status = 0 := by
    have := accepted_ok hA (by omega) _ (Array.getElem_mem (i := k) (by omega))
    rw [← getElem!_pos _ k (by omega), hcell] at this
    exact this
  have hp := (sweep_index (n := n) (axisY := axisY) (by rw [← hsize]; exact hk)
    (by rw [← hsize]; exact hlt)).2.2.2.2
  obtain ⟨hs, hv⟩ := firstLineStep_parts hp h0 (axisComponent axisY c)
  have hold : stateAt (lineState n.toNat axisY grid (lineOf n.toNat axisY k)
      (positionOf n.toNat axisY k)) (axisComponent axisY c) = stateAt grid[k]!.state c := by
    rw [lineState, stateAt_oriented, lineIndex_of]
  rw [hold] at hs hv
  rw [hcell, stateAt_cellOf]
  exact ⟨hs, hv⟩

/-- The flux through the boundary over a first-order step with ratio `r` from `grid`. -/
noncomputable def firstStepFlux (n : UInt64) (r : Float) (grid : Array Cell) (c : Fin 4) : ℝ :=
  real r * (boundary n.toNat false (firstLineFace n.toNat false grid) c +
    boundary n.toNat true (firstLineFace n.toNat true (sweep n false r grid)) c)

/-- The rounding residual of a first-order step. -/
noncomputable def firstStepResidual (n : UInt64) (r : Float) (grid : Array Cell) (c : Fin 4) : ℝ :=
  residual n.toNat false r (firstLineFace n.toNat false grid) grid (sweep n false r grid) c +
    residual n.toNat true r (firstLineFace n.toNat true (sweep n false r grid))
      (sweep n false r grid) (sweep n true r (sweep n false r grid)) c

/-- The bound on the rounding residual of a first-order step. -/
noncomputable def firstStepBound (n : UInt64) (r : Float) (grid : Array Cell) (c : Fin 4) : ℝ :=
  residualBound n.toNat false r (firstLineFace n.toNat false grid) grid c +
    residualBound n.toNat true r (firstLineFace n.toNat true (sweep n false r grid))
      (sweep n false r grid) c

theorem step_balance {n : UInt64} {ratio : Float} {grid : Array Cell}
    (hsize : grid.size = n.toNat * n.toNat) (hlt : grid.size < 2 ^ 64)
    (hA : accepted (step n ratio grid) = true) (c : Fin 4) :
    total (step n ratio grid) c =
        total grid c - firstStepFlux n ratio grid c + firstStepResidual n ratio grid c ∧
      |firstStepResidual n ratio grid c| ≤ firstStepBound n ratio grid c := by
  have hmid := sweep_size n false ratio grid hlt
  unfold step finishStep at hA ⊢
  split
  · rename_i hM
    rw [ite_eq_left hM] at hA
    have bx := sweep_balance n false ratio grid hsize hlt c
    have by' := sweep_balance n true ratio (sweep n false ratio grid) (by rw [hmid, hsize])
      (by rw [hmid]; exact hlt) c
    have rx := sweep_residual_le hsize hlt hM c
    have ry := sweep_residual_le (by rw [hmid, hsize]) (by rw [hmid]; exact hlt) hA c
    refine ⟨?_, ?_⟩
    · rw [by', bx]
      unfold firstStepFlux firstStepResidual
      ring
    · unfold firstStepResidual firstStepBound
      exact (abs_add_le _ _).trans (add_le_add rx ry)
  · rename_i hM
    rw [ite_eq_right hM] at hA
    exact absurd hA hM

/-! The balance of a run. -/

/-- An accepted first-order step from `b` to `b'` with ratio `r` on a grid of `n * n` cells with
`n ≤ 800`: the time advances by a positive `dt`, `r` is `dt / spacing n` in binary64, and the grid
becomes the accepted grid that `step` computes. -/
def FirstStep (n : UInt64) (b b' : Float × Array Cell) (r : Float) : Prop :=
  ∃ dt : Float, positive dt = true ∧ b'.1 = b.1 + dt ∧ r = dt / spacing n ∧
    b'.2 = step n r b.2 ∧ accepted b'.2 = true ∧ b.2.size = n.toNat * n.toNat ∧ n.toNat ≤ 800

theorem attempt_step {n : UInt64} {time dt : Float} {grid : Array Cell}
    (h : (attempt n time dt grid).1 = 0) :
    positive (attempt n time dt grid).2.1 = true ∧
      (attempt n time dt grid).2.2 = step n ((attempt n time dt grid).2.1 / spacing n) grid ∧
      accepted (attempt n time dt grid).2.2 = true := by
  unfold attempt at h ⊢
  split
  · rename_i hV
    rw [ite_eq_left hV] at h
    unfold tryStep at h ⊢
    dsimp only at h ⊢
    split
    · rename_i hA
      exact ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hV).1).1, rfl, hA⟩
    · rename_i hA
      rw [ite_eq_right hA] at h
      simp at h
  · rename_i hV
    rw [ite_eq_right hV] at h
    simp at h

/-- `attempt` with a status other than 0 returns its grid. -/
theorem attempt_keep {n : UInt64} {time dt : Float} {grid : Array Cell}
    (h : (attempt n time dt grid).1 ≠ 0) : (attempt n time dt grid).2.2 = grid := by
  unfold attempt at h ⊢
  split
  · rename_i hV
    rw [ite_eq_left hV] at h
    unfold tryStep at h ⊢
    dsimp only at h ⊢
    split
    · rename_i hA
      rw [ite_eq_left hA] at h
      exact absurd rfl h
    · rfl
  · rfl

theorem advanceWith_step {n : UInt64} {time dt : Float} {grid : Array Cell}
    (h : (advanceWith n time dt grid).1 = 0) :
    ∃ dt' : Float, positive dt' = true ∧ (advanceWith n time dt grid).2.1 = time + dt' ∧
      (advanceWith n time dt grid).2.2 = step n (dt' / spacing n) grid ∧
      accepted (advanceWith n time dt grid).2.2 = true := by
  obtain ⟨cond, step', hCondEq, hStepEq, hDef⟩ := advanceWith_loop n time dt grid
  have hInv := repeatWhile_inv (P := fun s : UInt64 × Float × Array Cell =>
      (s.1 ≠ 0 → s.2.2 = grid) ∧ (s.1 = 0 →
      positive s.2.1 = true ∧ s.2.2 = step n (s.2.1 / spacing n) grid ∧ accepted s.2.2 = true))
    (cond := cond) (step := step') (x0 := ((9 : UInt64), dt, grid)) 2048 ⟨fun _ => rfl, by simp⟩
    (fun x hc hx => by
      rw [hStepEq]
      have h9 : x.1 ≠ 0 := by
        rw [hCondEq] at hc
        intro h0
        simp [h0] at hc
      have hGrid := hx.1 h9
      refine ⟨fun hs => (attempt_keep hs).trans hGrid, fun hs => ?_⟩
      obtain ⟨h1, h2, h3⟩ := attempt_step hs
      exact ⟨h1, by rw [h2, hGrid], h3⟩)
  rw [hDef] at h ⊢
  generalize LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid) cond step' = R at h hInv ⊢
  obtain ⟨status, dt', g⟩ := R
  dsimp only at h hInv ⊢
  split
  · rename_i hS
    obtain ⟨hp, ht, ha⟩ := hInv.2 (by simpa using hS)
    exact ⟨dt', hp, rfl, ht, ha⟩
  · rename_i hS
    rw [ite_eq_right hS] at h
    split at h
    · simp at h
    · simp only at h
      exact absurd (by simp [h]) hS

theorem advanceStep_step {n status : UInt64} {time : Float} {grid : Array Cell}
    (h : (advanceStep n status time grid).1 = 0) (hsize : grid.size = n.toNat * n.toNat)
    (h800 : n.toNat ≤ 800) :
    ∃ r, FirstStep n (time, grid) ((advanceStep n status time grid).2.1,
      (advanceStep n status time grid).2.2) r := by
  unfold advanceStep at h ⊢
  dsimp only at h ⊢
  split
  · rename_i hS
    rw [ite_eq_left hS] at h
    obtain ⟨dt, hp, ht, hg, hA⟩ := advanceWith_step h
    exact ⟨_, dt, hp, ht, rfl, hg, hA, hsize, h800⟩
  · rename_i hS
    rw [ite_eq_right hS] at h
    simp at h

/-- A first-order run with `n ≤ 800` that returns status 0 is a chain of accepted steps from
time 0 and the initial grid. -/
theorem runFrom_steps {n : UInt64} (h800 : n.toNat ≤ 800) (h : (runFrom n).1 = 0) :
    Relation.ReflTransGen (fun a b => ∃ r, FirstStep n a b r) (0, initialCells n)
      ((runFrom n).2.1, (runFrom n).2.2) := by
  obtain ⟨cond, step', hCondEq, hStepEq, hDef⟩ := runFrom_loop n
  have hnn : (n * n).toNat = n.toNat * n.toNat := by
    rw [UInt64.toNat_mul]
    exact Nat.mod_eq_of_lt (by
      have : n.toNat * n.toNat ≤ 800 * 800 := Nat.mul_le_mul h800 h800
      omega)
  have hN : (n * n).toNat < 2 ^ 64 := (n * n).toNat_lt
  have hInv := repeatWhile_inv (P := fun s : UInt64 × Float × Array Cell =>
      s.2.2.size = (n * n).toNat ∧
        (s.1 = 0 → Relation.ReflTransGen (fun a b => ∃ r, FirstStep n a b r) (0, initialCells n)
          (s.2.1, s.2.2)))
    (cond := cond) (step := step') (x0 := ((0 : UInt64), (0 : Float), initialCells n))
    4294967296 ⟨initialCells_size n, fun _ => .refl⟩
    (fun x hc hx => by
      rw [hStepEq]
      have hc' : x.1 = 0 := by
        rw [hCondEq] at hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact hc.1
      have hs1 := hx.1
      refine ⟨(advanceStep_size (by omega)).trans hs1, fun hs => ?_⟩
      exact (hx.2 hc').tail (advanceStep_step hs (hs1.trans hnn) h800))
  rw [hDef] at h ⊢
  generalize LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n) cond
    step' = R at h hInv ⊢
  obtain ⟨status, time, grid⟩ := R
  dsimp only at h hInv ⊢
  split at h
  · simp at h
  · rename_i hT
    rw [ite_eq_right hT]
    subst h
    exact hInv.2 rfl

/-- A first-order run that returns status 0 is a trace of accepted steps from time 0 and the
initial grid, over which every component balances: its final total is its initial total, minus
the flux through the boundary summed over the steps, plus a rounding residual of at most the
sum of the step bounds. -/
theorem run_balance {n : UInt64} (h : (Examples.Euler.run n).1 = 0) :
    ∃ steps, Trace (FirstStep n) (0, initialCells n)
        ((Examples.Euler.run n).2.1, (Examples.Euler.run n).2.2) steps ∧
      ∀ c : Fin 4,
        total (Examples.Euler.run n).2.2 c = total (initialCells n) c -
            traceSum (fun r g => firstStepFlux n r g c) steps +
            traceSum (fun r g => firstStepResidual n r g c) steps ∧
          |traceSum (fun r g => firstStepResidual n r g c) steps| ≤
            traceSum (fun r g => firstStepBound n r g c) steps := by
  have h800 : n.toNat ≤ 800 := by
    have := (run_ok h).2.1
    exact UInt64.le_iff_toNat_le.mp this
  have hchain : Relation.ReflTransGen (fun a b => ∃ r, FirstStep n a b r) (0, initialCells n)
      ((Examples.Euler.run n).2.1, (Examples.Euler.run n).2.2) := by
    unfold Examples.Euler.run at h ⊢
    split at h
    · rename_i hn
      rw [ite_eq_left hn]
      exact runFrom_steps h800 h
    · simp at h
  obtain ⟨steps, ht⟩ := trace_of_chain (S := FirstStep n) (fun _ _ hs => hs) hchain
  refine ⟨steps, ht, ht.balance (fun b b' r hs c => ?_)⟩
  obtain ⟨-, -, -, -, hg, hA, hsize, h800'⟩ := hs
  rw [hg] at hA ⊢
  have hlt : b.2.size < 2 ^ 64 := by
    rw [hsize]
    have : n.toNat * n.toNat ≤ 800 * 800 := Nat.mul_le_mul h800' h800'
    omega
  exact step_balance hsize hlt hA c

end Examples.Euler
