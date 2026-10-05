import Project.Euler.Balance
import Project.Euler.Cfl

/-! Conservation balance of the reconstructed solver: of a sweep, of an accepted step, and of a
run that returns status 0. -/

namespace Project.Euler

open LeanExe.Examples.Euler Project.ProofKit
open CodeLib.IEEE64 (value Finite)

/-- The flux at the face between `b` and `c`: the Rusanov flux between the reconstructed state of
`b` on its right face, from `a`, `b`, and `c`, and the reconstructed state of `c` on its left face,
from `b`, `c`, and `d`. -/
def faceFlux (trials : UInt64) (a b c d : Conserved) : Flux :=
  outwardFlux (reconstruct trials a b c).right.density (reconstruct trials a b c).right.mx
    (reconstruct trials a b c).right.my (reconstruct trials a b c).right.energy
    (reconstruct trials b c d).left.density (reconstruct trials b c d).left.mx
    (reconstruct trials b c d).left.my (reconstruct trials b c d).left.energy

/-- An accepted step of the center of five states updates each component with the fluxes at its
two faces. -/
theorem reconstructedStep_parts {trials : UInt64} {ratio : Float} {a b c d e : Conserved}
    (h : (reconstructedStep trials ratio a b c d e).status = 0) (k : Fin 4) :
    (update ratio (stateAt c k) (fluxAt (faceFlux trials a b c d) k)
        (fluxAt (faceFlux trials b c d e) k)).status = 0 ∧
      updatedAt (reconstructedStep trials ratio a b c d e) k =
        (update ratio (stateAt c k) (fluxAt (faceFlux trials a b c d) k)
          (fluxAt (faceFlux trials b c d e) k)).value := by
  unfold reconstructedStep at h ⊢
  dsimp only at h ⊢
  have hc := rejectedCell_status h
  rw [ite_eq_left hc] at h ⊢
  unfold faceStep at h ⊢
  dsimp only at h ⊢
  have hc2 := rejectedCell_status h
  rw [ite_eq_left hc2]
  obtain ⟨h1, -⟩ := Bool.and_eq_true_iff.mp hc2
  obtain ⟨-, hn⟩ := Bool.and_eq_true_iff.mp h1
  obtain ⟨hn3, he⟩ := Bool.and_eq_true_iff.mp hn
  obtain ⟨hn2, ht⟩ := Bool.and_eq_true_iff.mp hn3
  obtain ⟨hd, hm⟩ := Bool.and_eq_true_iff.mp hn2
  fin_cases k
  · exact ⟨beq_iff_eq.mp hd, rfl⟩
  · exact ⟨beq_iff_eq.mp hm, rfl⟩
  · exact ⟨beq_iff_eq.mp ht, rfl⟩
  · exact ⟨beq_iff_eq.mp he, rfl⟩

/-- The state at position `q` of line `l`, as seen along the axis. -/
def lineState (m : Nat) (axisY : Bool) (grid : Array Cell) (l q : Nat) : Conserved :=
  oriented axisY grid[lineIndex m axisY l q]!.state

/-- The update of position `p` of line `l` from the five positions around it, clamped at the
ends of the line. -/
def lineStep (m : Nat) (axisY : Bool) (trials : UInt64) (ratio : Float) (grid : Array Cell)
    (l p : Nat) : Updated :=
  reconstructedStep trials ratio (lineState m axisY grid l (p - 2))
    (lineState m axisY grid l (p - 1)) (lineState m axisY grid l p)
    (lineState m axisY grid l (min (p + 1) (m - 1))) (lineState m axisY grid l (min (p + 2) (m - 1)))

/-- The cell at position `p` of line `l` after a sweep. -/
def sweepCell (m : Nat) (axisY : Bool) (trials : UInt64) (ratio : Float) (grid : Array Cell)
    (l p : Nat) : Cell :=
  let out := lineStep m axisY trials ratio grid l p
  ⟨⟨out.density, if axisY then out.transverse else out.momentum,
    if axisY then out.momentum else out.transverse, out.energy⟩, out.pressure, out.status⟩

/-- The cell at index `k` of a sweep is the cell at its position on its line. -/
theorem reconstructedSweep_cell {n : UInt64} {axisY : Bool} {trials : UInt64} {ratio : Float}
    {grid : Array Cell} (hsize : grid.size = n.toNat * n.toNat) (hlt : grid.size < 2 ^ 64)
    {k : Nat} (hk : k < grid.size) :
    (reconstructedSweep n axisY trials ratio grid)[k]! =
      sweepCell n.toNat axisY trials ratio grid (lineOf n.toNat axisY k)
        (positionOf n.toNat axisY k) := by
  have hsz := reconstructedSweep_size n axisY trials ratio grid hlt
  rw [getElem!_pos _ k (by omega)]
  unfold reconstructedSweep LeanExe.build
  rw [Array.getElem_ofFn]
  dsimp only
  obtain ⟨hc', hs', hX, hB, hp⟩ := sweep_index (axisY := axisY) (k := k) (by rw [← hsize]; exact hk)
    (by rw [← hsize]; exact hlt)
  set m := n.toNat with hmdef
  set l := lineOf m axisY k
  set p := positionOf m axisY k
  generalize (if axisY = true then UInt64.ofNat k / n else UInt64.ofNat k % n) = c at hc' ⊢
  generalize (if axisY = true then n else 1) = stride at hs' ⊢
  obtain ⟨hL, hLc⟩ := step_down hX hc' hs'
  generalize hlo : (if c == 0 then UInt64.ofNat k else UInt64.ofNat k - stride) = lower at hL ⊢
  generalize hlc : (if c == 0 then c else c - 1) = lowerCoordinate at hLc ⊢
  obtain ⟨hFL, -⟩ := step_down hL hLc hs'
  obtain ⟨hU, hUc⟩ := step_up hX hc' hs' hmdef.symm hp hB
  generalize hup : (if c + 1 < n then UInt64.ofNat k + stride else UInt64.ofNat k) = upper at hU ⊢
  generalize huc : (if c + 1 < n then c + 1 else c) = upperCoordinate at hUc ⊢
  obtain ⟨hFU, -⟩ := step_up hU hUc hs' hmdef.symm (by omega) hB
  rw [hFL, hL, hFU, hU, hX, show p - 1 - 1 = p - 2 by omega,
    show min (min (p + 1) (m - 1) + 1) (m - 1) = min (p + 2) (m - 1) by omega]
  rfl

/-! The balance of a sweep. -/

/-- The flux at face `j` of line `l`, between positions `j - 1` and `j`, from the four positions
around it, clamped at the ends of the line. -/
def lineFace (m : Nat) (axisY : Bool) (trials : UInt64) (grid : Array Cell) (l j : Nat) : Flux :=
  faceFlux trials (lineState m axisY grid l (j - 2)) (lineState m axisY grid l (j - 1))
    (lineState m axisY grid l (min j (m - 1))) (lineState m axisY grid l (min (j + 1) (m - 1)))

theorem stateAt_sweepCell (m : Nat) (axisY : Bool) (trials : UInt64) (ratio : Float)
    (grid : Array Cell) (l p : Nat) (c : Fin 4) :
    stateAt (sweepCell m axisY trials ratio grid l p).state c =
      updatedAt (lineStep m axisY trials ratio grid l p) (axisComponent axisY c) := by
  cases axisY <;> fin_cases c <;> rfl

/-- An accepted update of a position updates each component with the fluxes at the two faces
of the position. -/
theorem lineStep_parts {m : Nat} {axisY : Bool} {trials : UInt64} {ratio : Float}
    {grid : Array Cell} {l p : Nat} (hp : p < m)
    (h : (lineStep m axisY trials ratio grid l p).status = 0) (c : Fin 4) :
    (update ratio (stateAt (lineState m axisY grid l p) c)
        (fluxAt (lineFace m axisY trials grid l p) c)
        (fluxAt (lineFace m axisY trials grid l (p + 1)) c)).status = 0 ∧
      updatedAt (lineStep m axisY trials ratio grid l p) c =
        (update ratio (stateAt (lineState m axisY grid l p) c)
          (fluxAt (lineFace m axisY trials grid l p) c)
          (fluxAt (lineFace m axisY trials grid l (p + 1)) c)).value := by
  have hface : lineFace m axisY trials grid l p = faceFlux trials (lineState m axisY grid l (p - 2))
      (lineState m axisY grid l (p - 1)) (lineState m axisY grid l p)
      (lineState m axisY grid l (min (p + 1) (m - 1))) := by
    simp only [lineFace, show min p (m - 1) = p by omega]
  have hface' : lineFace m axisY trials grid l (p + 1) = faceFlux trials
      (lineState m axisY grid l (p - 1)) (lineState m axisY grid l p)
      (lineState m axisY grid l (min (p + 1) (m - 1)))
      (lineState m axisY grid l (min (p + 2) (m - 1))) := by
    simp only [lineFace, show p + 1 - 2 = p - 1 by omega, show p + 1 - 1 = p by omega,
      show p + 1 + 1 = p + 2 by omega]
  rw [hface, hface']
  exact reconstructedStep_parts h c

/-- The balance of a reconstructed sweep. -/
theorem reconstructedSweep_balance (n : UInt64) (axisY : Bool) (trials : UInt64) (ratio : Float)
    (grid : Array Cell) (hsize : grid.size = n.toNat * n.toNat) (hlt : grid.size < 2 ^ 64)
    (c : Fin 4) :
    total (reconstructedSweep n axisY trials ratio grid) c =
      total grid c - real ratio * boundary n.toNat axisY (lineFace n.toNat axisY trials grid) c +
        residual n.toNat axisY ratio (lineFace n.toNat axisY trials grid) grid
          (reconstructedSweep n axisY trials ratio grid) c :=
  balance_identity hsize (reconstructedSweep_size n axisY trials ratio grid hlt) c

/-- The rounding residual of an accepted reconstructed sweep is at most `residualBound`. -/
theorem reconstructedSweep_residual_le {n : UInt64} {axisY : Bool} {trials : UInt64}
    {ratio : Float} {grid : Array Cell} (hsize : grid.size = n.toNat * n.toNat)
    (hlt : grid.size < 2 ^ 64) (hA : accepted (reconstructedSweep n axisY trials ratio grid) = true)
    (c : Fin 4) :
    |residual n.toNat axisY ratio (lineFace n.toNat axisY trials grid) grid
        (reconstructedSweep n axisY trials ratio grid) c| ≤
      residualBound n.toNat axisY ratio (lineFace n.toNat axisY trials grid) grid c := by
  have hsz := reconstructedSweep_size n axisY trials ratio grid hlt
  refine residual_le (fun k hk c => ?_) c
  have hcell := reconstructedSweep_cell (axisY := axisY) (trials := trials) (ratio := ratio)
    hsize hlt hk
  have h0 : (sweepCell n.toNat axisY trials ratio grid (lineOf n.toNat axisY k)
      (positionOf n.toNat axisY k)).status = 0 := by
    rw [← hcell, getElem!_pos _ k (by omega)]
    exact accepted_ok hA (by omega) _ (Array.getElem_mem _)
  have hp := (sweep_index (n := n) (axisY := axisY) (by rw [← hsize]; exact hk)
    (by rw [← hsize]; exact hlt)).2.2.2.2
  obtain ⟨hs, hv⟩ := lineStep_parts hp h0 (axisComponent axisY c)
  have hold : stateAt (lineState n.toNat axisY grid (lineOf n.toNat axisY k)
      (positionOf n.toNat axisY k)) (axisComponent axisY c) = stateAt grid[k]!.state c := by
    rw [lineState, stateAt_oriented, lineIndex_of]
  rw [hold] at hs hv
  rw [hcell, stateAt_sweepCell]
  exact ⟨hs, hv⟩

/-! The balance of steps and runs. -/

/-- The flux through the boundary over a step with ratio `r` from `grid`: the x sweep of `grid`
and the y sweep of the grid it produces. -/
noncomputable def stepFlux (n trials : UInt64) (r : Float) (grid : Array Cell) (c : Fin 4) : ℝ :=
  real r * (boundary n.toNat false (lineFace n.toNat false trials grid) c +
    boundary n.toNat true (lineFace n.toNat true trials (reconstructedSweep n false trials r grid)) c)

/-- The rounding residual of a step. -/
noncomputable def stepResidual (n trials : UInt64) (r : Float) (grid : Array Cell) (c : Fin 4) :
    ℝ :=
  residual n.toNat false r (lineFace n.toNat false trials grid) grid
      (reconstructedSweep n false trials r grid) c +
    residual n.toNat true r
      (lineFace n.toNat true trials (reconstructedSweep n false trials r grid))
      (reconstructedSweep n false trials r grid)
      (reconstructedSweep n true trials r (reconstructedSweep n false trials r grid)) c

/-- The bound on the rounding residual of a step. -/
noncomputable def stepBound (n trials : UInt64) (r : Float) (grid : Array Cell) (c : Fin 4) : ℝ :=
  residualBound n.toNat false r (lineFace n.toNat false trials grid) grid c +
    residualBound n.toNat true r
      (lineFace n.toNat true trials (reconstructedSweep n false trials r grid))
      (reconstructedSweep n false trials r grid) c

/-- The total of a component after an accepted step is the total before, minus the flux through
the boundary, plus a rounding residual of at most `stepBound`. -/
theorem stepGrid_balance {n trials : UInt64} {ratio : Float} {grid : Array Cell}
    (hsize : grid.size = n.toNat * n.toNat) (hlt : grid.size < 2 ^ 64)
    (hA : accepted (reconstructedStepGrid n trials ratio grid) = true) (c : Fin 4) :
    total (reconstructedStepGrid n trials ratio grid) c =
        total grid c - stepFlux n trials ratio grid c + stepResidual n trials ratio grid c ∧
      |stepResidual n trials ratio grid c| ≤ stepBound n trials ratio grid c := by
  have hmid := reconstructedSweep_size n false trials ratio grid hlt
  unfold reconstructedStepGrid reconstructedFinish at hA ⊢
  split
  · rename_i hM
    rw [ite_eq_left hM] at hA
    have bx := reconstructedSweep_balance n false trials ratio grid hsize hlt c
    have by' := reconstructedSweep_balance n true trials ratio
      (reconstructedSweep n false trials ratio grid) (by rw [hmid, hsize]) (by rw [hmid]; exact hlt) c
    have rx := reconstructedSweep_residual_le hsize hlt hM c
    have ry := reconstructedSweep_residual_le (by rw [hmid, hsize]) (by rw [hmid]; exact hlt) hA c
    refine ⟨?_, ?_⟩
    · rw [by', bx]
      unfold stepFlux stepResidual
      ring
    · unfold stepResidual stepBound
      exact (abs_add_le _ _).trans (add_le_add rx ry)
  · rename_i hM
    rw [ite_eq_right hM] at hA
    exact absurd hA hM

/-- The steps of a run with their ratios and the grids they start from. -/
inductive StepTrace (n trials : UInt64) :
    Float × Array Cell → Float × Array Cell → List (Float × Array Cell) → Prop
  | refl (a : Float × Array Cell) : StepTrace n trials a a []
  | tail {a b b' : Float × Array Cell} {steps : List (Float × Array Cell)} (r : Float) :
      StepTrace n trials a b steps → AcceptedStep n trials b b' →
      b'.2 = reconstructedStepGrid n trials r b.2 →
      StepTrace n trials a b' (steps ++ [(r, b.2)])

theorem stepTrace_of_steps {n trials : UInt64} {a b : Float × Array Cell}
    (h : Relation.ReflTransGen (AcceptedStep n trials) a b) :
    ∃ steps, StepTrace n trials a b steps := by
  induction h with
  | refl => exact ⟨[], .refl _⟩
  | tail _ hs ih =>
    obtain ⟨steps, ht⟩ := ih
    have hs' := hs
    obtain ⟨-, r, -, -, hg, -⟩ := hs'
    exact ⟨_, .tail r ht hs hg⟩

/-- Over a trace of accepted steps, the total of a component changes by minus the flux through
the boundary, summed over the steps, plus a rounding residual of at most the sum of the step
bounds. -/
theorem StepTrace.balance {n trials : UInt64} {a b : Float × Array Cell}
    {steps : List (Float × Array Cell)} (h : StepTrace n trials a b steps) (c : Fin 4) :
    total b.2 c = total a.2 c - traceSum (fun r g => stepFlux n trials r g c) steps +
        traceSum (fun r g => stepResidual n trials r g c) steps ∧
      |traceSum (fun r g => stepResidual n trials r g c) steps| ≤
        traceSum (fun r g => stepBound n trials r g c) steps := by
  induction h with
  | refl => simp [traceSum]
  | @tail b0 b1 _ r _ hs hg ih =>
    obtain ⟨-, -, -, -, hg', hA, -, h800, hsize, -⟩ := hs
    rw [hg] at hA
    have hlt : b0.2.size < 2 ^ 64 := by
      rw [hsize]
      have : _ ≤ 800 * 800 := Nat.mul_le_mul h800 h800
      omega
    obtain ⟨hb, hr⟩ := stepGrid_balance hsize hlt hA c
    obtain ⟨ihb, ihr⟩ := ih
    simp only [traceSum, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] at ihb ihr ⊢
    refine ⟨?_, ?_⟩
    · rw [hg, hb, ihb]
      ring
    · exact (abs_add_le _ _).trans (add_le_add ihr hr)

/-- A reconstructed run that returns status 0 is a trace of accepted steps from time 0 and the
initial grid, over which every component balances: its final total is its initial total, minus
the flux through the boundary summed over the steps, plus a rounding residual of at most the
sum of the step bounds. -/
theorem reconstructedRun_balance {n trials : UInt64} (h : (reconstructedRun n trials).1 = 0) :
    ∃ steps, StepTrace n trials (0, initialCells n)
        ((reconstructedRun n trials).2.1, (reconstructedRun n trials).2.2) steps ∧
      ∀ c : Fin 4,
        total (reconstructedRun n trials).2.2 c = total (initialCells n) c -
            traceSum (fun r g => stepFlux n trials r g c) steps +
            traceSum (fun r g => stepResidual n trials r g c) steps ∧
          |traceSum (fun r g => stepResidual n trials r g c) steps| ≤
            traceSum (fun r g => stepBound n trials r g c) steps := by
  obtain ⟨steps, ht⟩ := stepTrace_of_steps (reconstructedRun_steps h)
  exact ⟨steps, ht, ht.balance⟩

end Project.Euler
