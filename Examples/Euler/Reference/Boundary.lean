import Examples.Euler.Reference.Accepted
import Examples.Euler.ReconstructedBalance
import Examples.Euler.FirstOrderBalance

/-! The boundary flux of each solver's balance against the exact Rusanov flux.  The balance of a
sweep subtracts the computed flux at the first and last faces of each line.  When the sweep is
accepted, each of those fluxes is within a bound computed from the words of the run of the exact
Rusanov flux `Rusanov.interfaceFlux` of the values of the two face states with the computed
speed.  A run that returns status 0 therefore changes the total of each component by minus the
exact boundary flux summed over its steps, plus a residual of at most the sum of the update
bounds and the boundary-flux bounds. -/

namespace Examples.Euler.Reference

open Examples.Euler LeanExe.ProofKit

/-! The boundary of a sweep, for any face flux. -/

/-- The reference flux through the last face of each line minus that through its first face,
summed over the lines. -/
noncomputable def referenceBoundary (m : Nat) (axisY : Bool) (reference : Nat → Nat → Fin 4 → ℝ)
    (c : Fin 4) : ℝ :=
  ∑ l ∈ Finset.range m,
    (reference l m (axisComponent axisY c) - reference l 0 (axisComponent axisY c))

/-- The sum over the lines of the bounds at the first and last faces. -/
noncomputable def boundaryBound (m : Nat) (axisY : Bool) (bound : Nat → Nat → Fin 4 → ℝ)
    (c : Fin 4) : ℝ :=
  ∑ l ∈ Finset.range m, (bound l m (axisComponent axisY c) + bound l 0 (axisComponent axisY c))

/-- When the flux at the first and last faces of every line is within `bound` of `reference`,
the boundary flux is within `boundaryBound` of the reference boundary flux. -/
theorem boundary_reference_le {m : Nat} {axisY : Bool} {face : Nat → Nat → Flux}
    {reference bound : Nat → Nat → Fin 4 → ℝ}
    (h : ∀ l < m, ∀ c, |real (fluxAt (face l 0) c) - reference l 0 c| ≤ bound l 0 c ∧
      |real (fluxAt (face l m) c) - reference l m c| ≤ bound l m c) (c : Fin 4) :
    |boundary m axisY face c - referenceBoundary m axisY reference c| ≤
      boundaryBound m axisY bound c := by
  unfold boundary referenceBoundary boundaryBound
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
  obtain ⟨h0, hm⟩ := h l (Finset.mem_range.mp hl) (axisComponent axisY c)
  rw [show ∀ a b x y : ℝ, a - b - (x - y) = (a - x) - (b - y) from fun _ _ _ _ => by ring]
  exact (abs_sub _ _).trans (add_le_add hm h0)

theorem lineIndex_position {m : Nat} {axisY : Bool} {l p : Nat} (hl : l < m) (hp : p < m) :
    lineIndex m axisY l p < m * m ∧ lineOf m axisY (lineIndex m axisY l p) = l ∧
      positionOf m axisY (lineIndex m axisY l p) = p := by
  have hm : 0 < m := by omega
  cases axisY
  · simp only [lineIndex, lineOf, positionOf, Bool.false_eq_true, ite_false, Nat.mul_one]
    have h1 : (l + 1) * m ≤ m * m := Nat.mul_le_mul_right m hl
    rw [Nat.add_mul, Nat.one_mul] at h1
    refine ⟨by omega, ?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hp, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
  · simp only [lineIndex, lineOf, positionOf, ite_true]
    have h1 : (p + 1) * m ≤ m * m := Nat.mul_le_mul_right m hp
    rw [Nat.add_mul, Nat.one_mul] at h1
    refine ⟨by omega, ?_, ?_⟩
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
    · rw [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hl, Nat.zero_add]

/-! The reconstructed solver. -/

/-- An accepted step of the center of five states accepts the fluxes at its two faces. -/
theorem reconstructedStep_faces {trials : UInt64} {ratio : Float} {a b c d e : Conserved}
    (h : (reconstructedStep trials ratio a b c d e).status = 0) :
    (faceFlux trials a b c d).status = 0 ∧ (faceFlux trials b c d e).status = 0 := by
  unfold reconstructedStep at h
  dsimp only at h
  have hc := rejectedCell_status h
  rw [ite_eq_left hc] at h
  unfold faceStep at h
  dsimp only at h
  have hc2 := rejectedCell_status h
  simp only [positive_eq, Bool.and_eq_true, beq_iff_eq, and_assoc] at hc2
  exact ⟨hc2.2.1, hc2.2.2.1⟩

theorem lineStep_faces {m : Nat} {axisY : Bool} {trials : UInt64} {ratio : Float}
    {grid : Array Cell} {l p : Nat} (hp : p < m)
    (h : (lineStep m axisY trials ratio grid l p).status = 0) :
    (lineFace m axisY trials grid l p).status = 0 ∧
      (lineFace m axisY trials grid l (p + 1)).status = 0 := by
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
  exact reconstructedStep_faces h

/-- An accepted sweep accepts the fluxes at the first and last faces of every line. -/
theorem reconstructedSweep_faces {n : UInt64} {axisY : Bool} {trials : UInt64} {ratio : Float}
    {grid : Array Cell} (hsize : grid.size = n.toNat * n.toNat) (hlt : grid.size < 2 ^ 64)
    (hA : accepted (reconstructedSweep n axisY trials ratio grid) = true) {l : Nat}
    (hl : l < n.toNat) :
    (lineFace n.toNat axisY trials grid l 0).status = 0 ∧
      (lineFace n.toNat axisY trials grid l n.toNat).status = 0 := by
  have hsz := reconstructedSweep_size n axisY trials ratio grid hlt
  have hcell : ∀ p < n.toNat, (lineStep n.toNat axisY trials ratio grid l p).status = 0 := by
    intro p hp
    obtain ⟨hk, hlk, hpk⟩ := lineIndex_position (axisY := axisY) hl hp
    have hc := reconstructedSweep_cell (axisY := axisY) (trials := trials) (ratio := ratio)
      hsize hlt (k := lineIndex n.toNat axisY l p) (by omega)
    rw [hlk, hpk] at hc
    have h0 := accepted_ok hA (by omega) _
      (Array.getElem_mem (i := lineIndex n.toNat axisY l p) (by omega))
    rw [← getElem!_pos _ _ (by omega), hc] at h0
    exact h0
  have hm : 0 < n.toNat := by omega
  obtain ⟨h0, -⟩ := lineStep_faces hm (hcell 0 hm)
  obtain ⟨-, h1⟩ := lineStep_faces (p := n.toNat - 1) (by omega) (hcell (n.toNat - 1) (by omega))
  rw [Nat.sub_add_cancel hm] at h1
  exact ⟨h0, h1⟩

/-- The exact Rusanov flux at face `j` of line `l` of the reconstructed solver: the flux of the
values of the two reconstructed face states with the computed speed. -/
noncomputable def lineReference (m : Nat) (axisY : Bool) (trials : UInt64) (grid : Array Cell)
    (l j : Nat) (c : Fin 4) : ℝ :=
  Equations.Rusanov.interfaceFlux (real (lineFace m axisY trials grid l j).alpha)
    (vec (reconstruct trials (lineState m axisY grid l (j - 2)) (lineState m axisY grid l (j - 1))
      (lineState m axisY grid l (min j (m - 1)))).right)
    (vec (reconstruct trials (lineState m axisY grid l (j - 1))
      (lineState m axisY grid l (min j (m - 1)))
      (lineState m axisY grid l (min (j + 1) (m - 1)))).left) c

/-- The error bound of the flux at face `j` of line `l` of the reconstructed solver. -/
noncomputable def lineFaceBound (m : Nat) (axisY : Bool) (trials : UInt64) (grid : Array Cell)
    (l j : Nat) (c : Fin 4) : ℝ :=
  let left := (reconstruct trials (lineState m axisY grid l (j - 2))
    (lineState m axisY grid l (j - 1)) (lineState m axisY grid l (min j (m - 1)))).right
  let right := (reconstruct trials (lineState m axisY grid l (j - 1))
    (lineState m axisY grid l (min j (m - 1))) (lineState m axisY grid l (min (j + 1) (m - 1)))).left
  outwardFluxErrorBound left.density left.mx left.my left.energy right.density right.mx right.my
    right.energy c

theorem lineFace_reference {m : Nat} {axisY : Bool} {trials : UInt64} {grid : Array Cell}
    {l j : Nat} (h : (lineFace m axisY trials grid l j).status = 0) (c : Fin 4) :
    |real (fluxAt (lineFace m axisY trials grid l j) c) - lineReference m axisY trials grid l j c| ≤
      lineFaceBound m axisY trials grid l j c :=
  outwardFlux_reference_residual h c

/-- The boundary flux of an accepted reconstructed sweep against the exact Rusanov flux. -/
theorem reconstructedSweep_boundary_reference {n : UInt64} {axisY : Bool} {trials : UInt64}
    {ratio : Float} {grid : Array Cell} (hsize : grid.size = n.toNat * n.toNat)
    (hlt : grid.size < 2 ^ 64) (hA : accepted (reconstructedSweep n axisY trials ratio grid) = true)
    (c : Fin 4) :
    |boundary n.toNat axisY (lineFace n.toNat axisY trials grid) c -
        referenceBoundary n.toNat axisY (lineReference n.toNat axisY trials grid) c| ≤
      boundaryBound n.toNat axisY (lineFaceBound n.toNat axisY trials grid) c :=
  boundary_reference_le (fun _ hl c => by
    obtain ⟨h0, hm⟩ := reconstructedSweep_faces hsize hlt hA hl
    exact ⟨lineFace_reference h0 c, lineFace_reference hm c⟩) c

theorem reconstructedStepGrid_sweeps {n trials : UInt64} {ratio : Float} {grid : Array Cell}
    (hA : accepted (reconstructedStepGrid n trials ratio grid) = true) :
    accepted (reconstructedSweep n false trials ratio grid) = true ∧
      accepted (reconstructedSweep n true trials ratio
        (reconstructedSweep n false trials ratio grid)) = true := by
  unfold reconstructedStepGrid reconstructedFinish at hA
  split at hA
  · rename_i hM
    exact ⟨hM, hA⟩
  · rename_i hM
    exact absurd hA hM

/-- The exact boundary flux over a reconstructed step with ratio `r` from `grid`. -/
noncomputable def stepReferenceFlux (n trials : UInt64) (r : Float) (grid : Array Cell)
    (c : Fin 4) : ℝ :=
  real r * (referenceBoundary n.toNat false (lineReference n.toNat false trials grid) c +
    referenceBoundary n.toNat true
      (lineReference n.toNat true trials (reconstructedSweep n false trials r grid)) c)

/-- The residual of a reconstructed step against the exact boundary flux: the rounding residual
of the updates plus the error of the computed boundary flux. -/
noncomputable def stepReferenceResidual (n trials : UInt64) (r : Float) (grid : Array Cell)
    (c : Fin 4) : ℝ :=
  stepResidual n trials r grid c + (stepReferenceFlux n trials r grid c - stepFlux n trials r grid c)

/-- The bound on `stepReferenceResidual`. -/
noncomputable def stepReferenceBound (n trials : UInt64) (r : Float) (grid : Array Cell)
    (c : Fin 4) : ℝ :=
  stepBound n trials r grid c + |real r| *
    (boundaryBound n.toNat false (lineFaceBound n.toNat false trials grid) c +
      boundaryBound n.toNat true
        (lineFaceBound n.toNat true trials (reconstructedSweep n false trials r grid)) c)

theorem reconstructedStep_reference_balance {n trials : UInt64} {b b' : Float × Array Cell}
    {r : Float} (h : ReconstructedStep n trials b b' r) (c : Fin 4) :
    total b'.2 c = total b.2 c - stepReferenceFlux n trials r b.2 c +
        stepReferenceResidual n trials r b.2 c ∧
      |stepReferenceResidual n trials r b.2 c| ≤ stepReferenceBound n trials r b.2 c := by
  obtain ⟨hb, hres⟩ := reconstructedStep_balance h c
  obtain ⟨⟨-, -, -, -, -, hA, -, h800, hsize, -⟩, hg⟩ := h
  rw [hg] at hA
  have hlt : b.2.size < 2 ^ 64 := by
    rw [hsize]
    have : n.toNat * n.toNat ≤ 800 * 800 := Nat.mul_le_mul h800 h800
    omega
  obtain ⟨hx, hy⟩ := reconstructedStepGrid_sweeps hA
  have hmid := reconstructedSweep_size n false trials r b.2 hlt
  have ex := reconstructedSweep_boundary_reference hsize hlt hx c
  have ey := reconstructedSweep_boundary_reference (by rw [hmid, hsize]) (by rw [hmid]; exact hlt)
    hy c
  refine ⟨?_, ?_⟩
  · rw [hb]
    unfold stepReferenceResidual
    ring
  · unfold stepReferenceResidual stepReferenceBound stepReferenceFlux stepFlux
    refine (abs_add_le _ _).trans (add_le_add hres ?_)
    rw [← mul_sub, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [show ∀ a b x y : ℝ, a + b - (x + y) = (a - x) + (b - y) from fun _ _ _ _ => by ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_sub_comm]
      exact ex
    · rw [abs_sub_comm]
      exact ey

/-- A reconstructed run that returns status 0 is a trace of accepted steps over which every
component balances against the exact boundary flux: its final total is its initial total, minus
the exact boundary flux summed over the steps, plus a residual of at most the sum of the step
bounds. -/
theorem reconstructedRun_reference_balance {n trials : UInt64}
    (h : (reconstructedRun n trials).1 = 0) :
    ∃ steps, Trace (ReconstructedStep n trials) (0, initialCells n)
        ((reconstructedRun n trials).2.1, (reconstructedRun n trials).2.2) steps ∧
      ∀ c : Fin 4,
        total (reconstructedRun n trials).2.2 c = total (initialCells n) c -
            traceSum (fun r g => stepReferenceFlux n trials r g c) steps +
            traceSum (fun r g => stepReferenceResidual n trials r g c) steps ∧
          |traceSum (fun r g => stepReferenceResidual n trials r g c) steps| ≤
            traceSum (fun r g => stepReferenceBound n trials r g c) steps := by
  obtain ⟨steps, ht, -⟩ := reconstructedRun_balance h
  exact ⟨steps, ht, ht.balance (fun _ _ _ hs => reconstructedStep_reference_balance hs)⟩

/-! The first-order solver. -/

/-- An accepted update of the center of three states accepts the fluxes at its two faces. -/
theorem advanceCell_faces {ratio : Float} {a b d : Conserved}
    (h : (advanceCell ratio a.density a.mx a.my a.energy b.density b.mx b.my b.energy d.density
      d.mx d.my d.energy).status = 0) :
    (stateFlux a b).status = 0 ∧ (stateFlux b d).status = 0 := by
  unfold advanceCell at h
  dsimp only at h
  have hc := rejectedCell_status h
  simp only [positive_eq, Bool.and_eq_true, beq_iff_eq, and_assoc] at hc
  exact ⟨hc.2.1, hc.2.2.1⟩

theorem firstLineStep_faces {m : Nat} {axisY : Bool} {ratio : Float} {grid : Array Cell}
    {l p : Nat} (hp : p < m) (h : (firstLineStep m axisY ratio grid l p).status = 0) :
    (firstLineFace m axisY grid l p).status = 0 ∧
      (firstLineFace m axisY grid l (p + 1)).status = 0 := by
  simp only [firstLineFace, show min p (m - 1) = p by omega, show p + 1 - 1 = p by omega]
  exact advanceCell_faces h

/-- An accepted first-order sweep accepts the fluxes at the first and last faces of every
line. -/
theorem sweep_faces {n : UInt64} {axisY : Bool} {ratio : Float} {grid : Array Cell}
    (hsize : grid.size = n.toNat * n.toNat) (hlt : grid.size < 2 ^ 64)
    (hA : accepted (sweep n axisY ratio grid) = true) {l : Nat} (hl : l < n.toNat) :
    (firstLineFace n.toNat axisY grid l 0).status = 0 ∧
      (firstLineFace n.toNat axisY grid l n.toNat).status = 0 := by
  have hsz := sweep_size n axisY ratio grid hlt
  have hcell : ∀ p < n.toNat, (firstLineStep n.toNat axisY ratio grid l p).status = 0 := by
    intro p hp
    obtain ⟨hk, hlk, hpk⟩ := lineIndex_position (axisY := axisY) hl hp
    have hc := sweep_cell (axisY := axisY) (ratio := ratio) hsize hlt
      (k := lineIndex n.toNat axisY l p) (by omega)
    rw [hlk, hpk] at hc
    have h0 := accepted_ok hA (by omega) _
      (Array.getElem_mem (i := lineIndex n.toNat axisY l p) (by omega))
    rw [← getElem!_pos _ _ (by omega), hc] at h0
    exact h0
  have hm : 0 < n.toNat := by omega
  obtain ⟨h0, -⟩ := firstLineStep_faces hm (hcell 0 hm)
  obtain ⟨-, h1⟩ := firstLineStep_faces (p := n.toNat - 1) (by omega)
    (hcell (n.toNat - 1) (by omega))
  rw [Nat.sub_add_cancel hm] at h1
  exact ⟨h0, h1⟩

/-- The exact Rusanov flux at face `j` of line `l` of the first-order solver: the flux of the
values of the two states beside the face with the computed speed. -/
noncomputable def firstLineReference (m : Nat) (axisY : Bool) (grid : Array Cell) (l j : Nat)
    (c : Fin 4) : ℝ :=
  Equations.Rusanov.interfaceFlux (real (firstLineFace m axisY grid l j).alpha)
    (vec (lineState m axisY grid l (j - 1))) (vec (lineState m axisY grid l (min j (m - 1)))) c

/-- The error bound of the flux at face `j` of line `l` of the first-order solver. -/
noncomputable def firstLineFaceBound (m : Nat) (axisY : Bool) (grid : Array Cell) (l j : Nat)
    (c : Fin 4) : ℝ :=
  let left := lineState m axisY grid l (j - 1)
  let right := lineState m axisY grid l (min j (m - 1))
  fluxErrorBound left.density left.mx left.my left.energy right.density right.mx right.my
    right.energy c

theorem firstLineFace_reference {m : Nat} {axisY : Bool} {grid : Array Cell} {l j : Nat}
    (h : (firstLineFace m axisY grid l j).status = 0) (c : Fin 4) :
    |real (fluxAt (firstLineFace m axisY grid l j) c) - firstLineReference m axisY grid l j c| ≤
      firstLineFaceBound m axisY grid l j c :=
  flux_reference_residual h c

/-- The boundary flux of an accepted first-order sweep against the exact Rusanov flux. -/
theorem sweep_boundary_reference {n : UInt64} {axisY : Bool} {ratio : Float} {grid : Array Cell}
    (hsize : grid.size = n.toNat * n.toNat) (hlt : grid.size < 2 ^ 64)
    (hA : accepted (sweep n axisY ratio grid) = true) (c : Fin 4) :
    |boundary n.toNat axisY (firstLineFace n.toNat axisY grid) c -
        referenceBoundary n.toNat axisY (firstLineReference n.toNat axisY grid) c| ≤
      boundaryBound n.toNat axisY (firstLineFaceBound n.toNat axisY grid) c :=
  boundary_reference_le (fun _ hl c => by
    obtain ⟨h0, hm⟩ := sweep_faces hsize hlt hA hl
    exact ⟨firstLineFace_reference h0 c, firstLineFace_reference hm c⟩) c

theorem step_sweeps {n : UInt64} {ratio : Float} {grid : Array Cell}
    (hA : accepted (step n ratio grid) = true) :
    accepted (sweep n false ratio grid) = true ∧
      accepted (sweep n true ratio (sweep n false ratio grid)) = true := by
  unfold step finishStep at hA
  split at hA
  · rename_i hM
    exact ⟨hM, hA⟩
  · rename_i hM
    exact absurd hA hM

/-- The exact boundary flux over a first-order step with ratio `r` from `grid`. -/
noncomputable def firstStepReferenceFlux (n : UInt64) (r : Float) (grid : Array Cell)
    (c : Fin 4) : ℝ :=
  real r * (referenceBoundary n.toNat false (firstLineReference n.toNat false grid) c +
    referenceBoundary n.toNat true (firstLineReference n.toNat true (sweep n false r grid)) c)

/-- The residual of a first-order step against the exact boundary flux. -/
noncomputable def firstStepReferenceResidual (n : UInt64) (r : Float) (grid : Array Cell)
    (c : Fin 4) : ℝ :=
  firstStepResidual n r grid c + (firstStepReferenceFlux n r grid c - firstStepFlux n r grid c)

/-- The bound on `firstStepReferenceResidual`. -/
noncomputable def firstStepReferenceBound (n : UInt64) (r : Float) (grid : Array Cell)
    (c : Fin 4) : ℝ :=
  firstStepBound n r grid c + |real r| *
    (boundaryBound n.toNat false (firstLineFaceBound n.toNat false grid) c +
      boundaryBound n.toNat true (firstLineFaceBound n.toNat true (sweep n false r grid)) c)

theorem firstStep_reference_balance {n : UInt64} {b b' : Float × Array Cell} {r : Float}
    (h : FirstStep n b b' r) (c : Fin 4) :
    total b'.2 c = total b.2 c - firstStepReferenceFlux n r b.2 c +
        firstStepReferenceResidual n r b.2 c ∧
      |firstStepReferenceResidual n r b.2 c| ≤ firstStepReferenceBound n r b.2 c := by
  obtain ⟨-, -, -, -, hg, hA, hsize, h800⟩ := h
  rw [hg] at hA ⊢
  have hlt : b.2.size < 2 ^ 64 := by
    rw [hsize]
    have : n.toNat * n.toNat ≤ 800 * 800 := Nat.mul_le_mul h800 h800
    omega
  obtain ⟨hb, hres⟩ := step_balance hsize hlt hA c
  obtain ⟨hx, hy⟩ := step_sweeps hA
  have hmid := sweep_size n false r b.2 hlt
  have ex := sweep_boundary_reference hsize hlt hx c
  have ey := sweep_boundary_reference (by rw [hmid, hsize]) (by rw [hmid]; exact hlt) hy c
  refine ⟨?_, ?_⟩
  · rw [hb]
    unfold firstStepReferenceResidual
    ring
  · unfold firstStepReferenceResidual firstStepReferenceBound firstStepReferenceFlux
      firstStepFlux
    refine (abs_add_le _ _).trans (add_le_add hres ?_)
    rw [← mul_sub, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [show ∀ a b x y : ℝ, a + b - (x + y) = (a - x) + (b - y) from fun _ _ _ _ => by ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_sub_comm]
      exact ex
    · rw [abs_sub_comm]
      exact ey

/-- A first-order run that returns status 0 is a trace of accepted steps over which every
component balances against the exact boundary flux: its final total is its initial total, minus
the exact boundary flux summed over the steps, plus a residual of at most the sum of the step
bounds. -/
theorem run_reference_balance {n : UInt64} (h : (Examples.Euler.run n).1 = 0) :
    ∃ steps, Trace (FirstStep n) (0, initialCells n)
        ((Examples.Euler.run n).2.1, (Examples.Euler.run n).2.2) steps ∧
      ∀ c : Fin 4,
        total (Examples.Euler.run n).2.2 c = total (initialCells n) c -
            traceSum (fun r g => firstStepReferenceFlux n r g c) steps +
            traceSum (fun r g => firstStepReferenceResidual n r g c) steps ∧
          |traceSum (fun r g => firstStepReferenceResidual n r g c) steps| ≤
            traceSum (fun r g => firstStepReferenceBound n r g c) steps := by
  obtain ⟨steps, ht, -⟩ := run_balance h
  exact ⟨steps, ht, ht.balance (fun _ _ _ hs => firstStep_reference_balance hs)⟩

end Examples.Euler.Reference
