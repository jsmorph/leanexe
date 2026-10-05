import Project.Euler.Cfl

/-! Conservation balance of the reconstructed solver.  A sweep updates each component of a cell
by `u' = u - r (F_right - F_left)` in three rounded operations, and the two cells beside a face
compute its flux from the same four states, so the computed fluxes telescope along a line.  The
residual of a cell, the difference between `u'` and the exact value of the formula on the
computed words, is bounded by the gaps between the neighbors of the three rounded words. -/

namespace Project.Euler

open LeanExe.Examples.Euler Project.ProofKit
open CodeLib.IEEE64 (value Finite)

/-- The distance between the neighbors of a word, which bounds the rounding error of an
operation whose finite result is the word. -/
noncomputable def gap (w : UInt64) : ℝ :=
  value (F64Adjacent.nextUp w) - value (F64Adjacent.nextDown w)

theorem enclosure_gap {x : ℝ} {w : UInt64} (hf : Finite w)
    (h : value (F64Adjacent.nextDown w) ≤ x ∧ x ≤ value (F64Adjacent.nextUp w)) :
    |x - value w| ≤ gap w := by
  have hd := F64Adjacent.nextDown_lt w hf
  have hu := F64Adjacent.nextUp_lt w hf
  rw [abs_le]
  unfold gap
  constructor <;> linarith [h.1, h.2]

theorem finite_bits {x : Float} (h : finite x = true) : Finite x.toBits :=
  (F64Order.finiteBits_iff x.toBits).mp h

/-- The rounding bound of `update`. -/
noncomputable def updateBound (ratio state fluxL fluxR : Float) : ℝ :=
  real ratio * gap (fluxR - fluxL).toBits + gap (ratio * (fluxR - fluxL)).toBits +
    gap (state - ratio * (fluxR - fluxL)).toBits

/-- An accepted update differs from `u - r (F_right - F_left)` on its words by at most
`updateBound`. -/
theorem update_balance {ratio state fluxL fluxR : Float}
    (h : (update ratio state fluxL fluxR).status = 0) :
    |real (update ratio state fluxL fluxR).value -
        (real state - real ratio * (real fluxR - real fluxL))| ≤
      updateBound ratio state fluxL fluxR := by
  unfold update at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i hc
    rw [ite_eq_left hc]
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨h3, hfR⟩ := Bool.and_eq_true_iff.mp h1
    obtain ⟨h4, hfL⟩ := Bool.and_eq_true_iff.mp h3
    obtain ⟨hr, hs⟩ := Bool.and_eq_true_iff.mp h4
    obtain ⟨h5, hv⟩ := Bool.and_eq_true_iff.mp h2
    obtain ⟨hd, hi⟩ := Bool.and_eq_true_iff.mp h5
    have hr' := real_pos_of_positive (by simpa [positive] using hr)
    have ed := enclosure_gap (finite_bits hd) (by
      rw [F64Bits.toBits_sub]
      exact F64Adjacent.sub_enclosure _ _ (finite_bits hfR) (finite_bits hfL)
        (by rw [← F64Bits.toBits_sub]; exact finite_bits hd))
    have ei := enclosure_gap (finite_bits hi) (by
      rw [F64Bits.toBits_mul]
      exact F64Adjacent.mul_enclosure _ _ (F64Order.positiveBits_spec _ (by
        simpa [positive, F64Order.positiveBits] using hr)).1 (finite_bits hd)
        (by rw [← F64Bits.toBits_mul]; exact finite_bits hi))
    have ev := enclosure_gap (finite_bits hv) (by
      rw [F64Bits.toBits_sub]
      exact F64Adjacent.sub_enclosure _ _ (finite_bits hs) (finite_bits hi)
        (by rw [← F64Bits.toBits_sub]; exact finite_bits hv))
    rw [F64Bits.toBits_sub, ← F64Bits.toBits_sub] at ed
    simp only [updateBound, real] at *
    rw [F64Bits.toBits_sub, F64Bits.toBits_mul, ← F64Bits.toBits_mul, ← F64Bits.toBits_sub] at *
    have hrd : |value ratio.toBits * (value fluxR.toBits - value fluxL.toBits) -
        value ratio.toBits * value (fluxR - fluxL).toBits| ≤
        value ratio.toBits * gap (fluxR - fluxL).toBits := by
      rw [← mul_sub, abs_mul, abs_of_pos hr']
      exact mul_le_mul_of_nonneg_left ed hr'.le
    rw [abs_le] at ed ei ev hrd ⊢
    constructor <;> linarith [ed.1, ed.2, ei.1, ei.2, ev.1, ev.2, hrd.1, hrd.2]
  · simp at h

/-- The four components of a state. -/
def stateAt (q : Conserved) : Fin 4 → Float := ![q.density, q.mx, q.my, q.energy]

/-- The four components of a flux. -/
def fluxAt (f : Flux) : Fin 4 → Float := ![f.mass, f.momentum, f.transverse, f.energy]

/-- The four components of an updated state. -/
def updatedAt (u : Updated) : Fin 4 → Float := ![u.density, u.momentum, u.transverse, u.energy]

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

/-! The cells of a sweep as positions on lines. -/

/-- The index of position `q` of line `l` of an `m × m` grid along an axis: rows along x,
columns along y. -/
def lineIndex (m : Nat) (axisY : Bool) (l q : Nat) : Nat :=
  (if axisY then l else l * m) + q * (if axisY then m else 1)

/-- The line of the cell at index `k`. -/
def lineOf (m : Nat) (axisY : Bool) (k : Nat) : Nat := if axisY then k % m else k / m

/-- The position of the cell at index `k` on its line. -/
def positionOf (m : Nat) (axisY : Bool) (k : Nat) : Nat := if axisY then k / m else k % m

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

theorem step_down {X c stride : UInt64} {B q s : Nat} (hX : X.toNat = B + q * s)
    (hc : c.toNat = q) (hs : stride.toNat = s) :
    (if c == 0 then X else X - stride).toNat = B + (q - 1) * s ∧
      (if c == 0 then c else c - 1).toNat = q - 1 := by
  by_cases hq : q = 0
  · have hc0 : c = 0 := UInt64.toNat_inj.mp (by rw [hc, hq]; rfl)
    subst hq
    simp [hc0, hX]
  · have hc0 : ¬c = 0 := fun h => hq (by rw [← hc, h]; rfl)
    have hqs : s ≤ q * s := Nat.le_mul_of_pos_left s (by omega)
    have hsub : (q - 1) * s = q * s - s := Nat.sub_one_mul q s
    simp only [beq_iff_eq, hc0, ite_false]
    refine ⟨?_, ?_⟩
    · rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hX, hs, hsub]
      omega
    · rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega)), hc]
      simp

theorem step_up {X c stride n : UInt64} {B q s m : Nat} (hX : X.toNat = B + q * s)
    (hc : c.toNat = q) (hs : stride.toNat = s) (hn : n.toNat = m) (hq : q < m)
    (hB : B + (m - 1) * s < 2 ^ 64) :
    (if c + 1 < n then X + stride else X).toNat = B + min (q + 1) (m - 1) * s ∧
      (if c + 1 < n then c + 1 else c).toNat = min (q + 1) (m - 1) := by
  have hc1 : (c + 1).toNat = q + 1 := by
    have := n.toNat_lt
    rw [UInt64.toNat_add, hc]
    simp only [UInt64.reduceToNat]
    omega
  by_cases hlt : q + 1 < m
  · have hl : c + 1 < n := UInt64.lt_iff_toNat_lt.mpr (by rw [hc1, hn]; exact hlt)
    simp only [hl, ite_true]
    have hmul : (q + 1) * s ≤ (m - 1) * s := Nat.mul_le_mul_right s (by omega)
    have hadd : (q + 1) * s = q * s + s := Nat.succ_mul q s
    refine ⟨?_, by rw [hc1]; omega⟩
    rw [UInt64.toNat_add, hX, hs, show min (q + 1) (m - 1) = q + 1 by omega]
    omega
  · have hl : ¬c + 1 < n := fun h => hlt (by
      have := UInt64.lt_iff_toNat_lt.mp h
      rwa [hc1, hn] at this)
    simp only [hl, ite_false]
    rw [show min (q + 1) (m - 1) = q by omega]
    exact ⟨hX, hc⟩

theorem lineIndex_of (m : Nat) (axisY : Bool) (k : Nat) :
    lineIndex m axisY (lineOf m axisY k) (positionOf m axisY k) = k := by
  cases axisY
  · simp [lineIndex, lineOf, positionOf, Nat.div_add_mod']
  · simp [lineIndex, lineOf, positionOf, Nat.mod_add_div']

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
  have hm : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h | h
    · rw [hsize, h] at hk; simp at hk
    · exact h
  have hK : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  set m := n.toNat with hmdef
  set l := lineOf m axisY k
  set p := positionOf m axisY k
  have hp : p < m := by
    simp only [p, positionOf]
    split
    · exact Nat.div_lt_of_lt_mul (by rw [← hsize]; exact hk)
    · exact Nat.mod_lt _ hm
  have hl : l < m := by
    simp only [l, lineOf]
    split
    · exact Nat.mod_lt _ hm
    · exact Nat.div_lt_of_lt_mul (by rw [← hsize]; exact hk)
  generalize hc : (if axisY = true then UInt64.ofNat k / n else UInt64.ofNat k % n) = c
  generalize hs : (if axisY = true then n else 1) = stride
  have hc' : c.toNat = p := by
    rw [← hc]
    simp only [p, positionOf]
    split <;> simp [UInt64.toNat_div, UInt64.toNat_mod, hK, ← hmdef]
  have hs' : stride.toNat = (if axisY then m else 1) := by
    rw [← hs]
    split <;> simp [← hmdef]
  have hX : (UInt64.ofNat k).toNat = (if axisY then l else l * m) + p * (if axisY then m else 1) := by
    rw [hK]
    exact (lineIndex_of m axisY k).symm
  have hB : (if axisY then l else l * m) + (m - 1) * (if axisY then m else 1) < 2 ^ 64 := by
    have : (if axisY then l else l * m) + (m - 1) * (if axisY then m else 1) < m * m := by
      cases axisY
      · simp only [Bool.false_eq_true, ite_false, Nat.mul_one]
        have : l * m + m ≤ m * m := by
          calc l * m + m = (l + 1) * m := by ring
            _ ≤ m * m := Nat.mul_le_mul_right m hl
        omega
      · simp only [ite_true]
        have : (m - 1) * m + m = m * m := by
          rw [Nat.sub_one_mul]
          have : m ≤ m * m := Nat.le_mul_of_pos_left m hm
          omega
        omega
    omega
  obtain ⟨hL, hLc⟩ := step_down hX hc' hs'
  generalize hlo : (if c == 0 then UInt64.ofNat k else UInt64.ofNat k - stride) = lower at hL ⊢
  generalize hlc : (if c == 0 then c else c - 1) = lowerCoordinate at hLc ⊢
  obtain ⟨hFL, -⟩ := step_down hL hLc hs'
  obtain ⟨hU, hUc⟩ := step_up hX hc' hs' hmdef.symm hp hB
  generalize hup : (if c + 1 < n then UInt64.ofNat k + stride else UInt64.ofNat k) = upper at hU ⊢
  generalize huc : (if c + 1 < n then c + 1 else c) = upperCoordinate at hUc ⊢
  obtain ⟨hFU, -⟩ := step_up hU hUc hs' hmdef.symm (by omega) hB
  rw [hFL, hL, hFU, hU, show (UInt64.ofNat k).toNat = lineIndex m axisY l p by
    rw [hK]; exact (lineIndex_of m axisY k).symm,
    show p - 1 - 1 = p - 2 by omega,
    show min (min (p + 1) (m - 1) + 1) (m - 1) = min (p + 2) (m - 1) by omega]
  rfl

/-! The balance of a sweep. -/

/-- The flux at face `j` of line `l`, between positions `j - 1` and `j`, from the four positions
around it, clamped at the ends of the line. -/
def lineFace (m : Nat) (axisY : Bool) (trials : UInt64) (grid : Array Cell) (l j : Nat) : Flux :=
  faceFlux trials (lineState m axisY grid l (j - 2)) (lineState m axisY grid l (j - 1))
    (lineState m axisY grid l (min j (m - 1))) (lineState m axisY grid l (min (j + 1) (m - 1)))

/-- The component along the axis that holds component `c` of a state: a y sweep exchanges the
momenta. -/
def axisComponent (axisY : Bool) (c : Fin 4) : Fin 4 := if axisY then ![0, 2, 1, 3] c else c

theorem stateAt_oriented (axisY : Bool) (q : Conserved) (c : Fin 4) :
    stateAt (oriented axisY q) (axisComponent axisY c) = stateAt q c := by
  cases axisY <;> fin_cases c <;> rfl

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

/-- A sum over the cells of an `m × m` grid as a sum over lines and positions. -/
theorem sum_rows (m : Nat) (h : ℕ → ℕ → ℝ) (a : Nat) :
    ∑ k ∈ Finset.range (a * m), h (k / m) (k % m) =
      ∑ l ∈ Finset.range a, ∑ q ∈ Finset.range m, h l q := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    have hq' := Finset.mem_range.mp hq
    have hm : 0 < m := by omega
    rw [show (a * m + q) / m = a by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hq', Nat.zero_add],
      show (a * m + q) % m = q by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq']]

theorem sum_lines (m : Nat) (axisY : Bool) (h : ℕ → ℕ → ℝ) :
    ∑ k ∈ Finset.range (m * m), h (lineOf m axisY k) (positionOf m axisY k) =
      ∑ l ∈ Finset.range m, ∑ q ∈ Finset.range m, h l q := by
  cases axisY
  · exact sum_rows m h m
  · rw [Finset.sum_comm]
    exact sum_rows m (fun a b => h b a) m

/-- The total of component `c` over the cells of a grid. -/
noncomputable def total (grid : Array Cell) (c : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range grid.size, real (stateAt grid[k]!.state c)

/-- The flux of component `c` at face `j` of line `l`. -/
noncomputable def faceValue (m : Nat) (axisY : Bool) (trials : UInt64) (grid : Array Cell)
    (c : Fin 4) (l j : Nat) : ℝ :=
  real (fluxAt (lineFace m axisY trials grid l j) (axisComponent axisY c))

/-- The flux through the last face of each line minus the flux through its first face, summed
over the lines. -/
noncomputable def sweepBoundary (m : Nat) (axisY : Bool) (trials : UInt64) (grid : Array Cell)
    (c : Fin 4) : ℝ :=
  ∑ l ∈ Finset.range m, (faceValue m axisY trials grid c l m - faceValue m axisY trials grid c l 0)

/-- The rounding residual of a sweep: over the cells, the new component minus the exact value
of `u - r (F_right - F_left)` on the computed words. -/
noncomputable def sweepResidual (n : UInt64) (axisY : Bool) (trials : UInt64) (ratio : Float)
    (grid : Array Cell) (c : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range grid.size,
    (real (stateAt (reconstructedSweep n axisY trials ratio grid)[k]!.state c) -
      (real (stateAt grid[k]!.state c) - real ratio *
        (faceValue n.toNat axisY trials grid c (lineOf n.toNat axisY k)
            (positionOf n.toNat axisY k + 1) -
          faceValue n.toNat axisY trials grid c (lineOf n.toNat axisY k)
            (positionOf n.toNat axisY k))))

/-- The bound on the rounding residual of a sweep. -/
noncomputable def sweepBound (n : UInt64) (axisY : Bool) (trials : UInt64) (ratio : Float)
    (grid : Array Cell) (c : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range grid.size,
    updateBound ratio
      (stateAt (lineState n.toNat axisY grid (lineOf n.toNat axisY k) (positionOf n.toNat axisY k))
        (axisComponent axisY c))
      (fluxAt (lineFace n.toNat axisY trials grid (lineOf n.toNat axisY k)
        (positionOf n.toNat axisY k)) (axisComponent axisY c))
      (fluxAt (lineFace n.toNat axisY trials grid (lineOf n.toNat axisY k)
        (positionOf n.toNat axisY k + 1)) (axisComponent axisY c))

/-- The total of a component after a sweep is the total before, minus the ratio times the flux
through the ends of the lines, plus the rounding residual. -/
theorem sweep_balance (n : UInt64) (axisY : Bool) (trials : UInt64) (ratio : Float)
    (grid : Array Cell) (hsize : grid.size = n.toNat * n.toNat) (hlt : grid.size < 2 ^ 64)
    (c : Fin 4) :
    total (reconstructedSweep n axisY trials ratio grid) c =
      total grid c - real ratio * sweepBoundary n.toNat axisY trials grid c +
        sweepResidual n axisY trials ratio grid c := by
  have hsz := reconstructedSweep_size n axisY trials ratio grid hlt
  have htel : ∑ k ∈ Finset.range grid.size,
      (faceValue n.toNat axisY trials grid c (lineOf n.toNat axisY k)
          (positionOf n.toNat axisY k + 1) -
        faceValue n.toNat axisY trials grid c (lineOf n.toNat axisY k)
          (positionOf n.toNat axisY k)) = sweepBoundary n.toNat axisY trials grid c := by
    rw [hsize, sum_lines n.toNat axisY
      (fun l q => faceValue n.toNat axisY trials grid c l (q + 1) -
        faceValue n.toNat axisY trials grid c l q)]
    unfold sweepBoundary
    apply Finset.sum_congr rfl
    intro l _
    exact Finset.sum_range_sub (fun q => faceValue n.toNat axisY trials grid c l q) n.toNat
  unfold total sweepResidual
  rw [hsz, ← htel, Finset.mul_sum]
  simp only [Finset.sum_sub_distrib]
  ring

/-- The rounding residual of an accepted sweep is at most `sweepBound` in magnitude. -/
theorem sweep_residual_le {n : UInt64} {axisY : Bool} {trials : UInt64} {ratio : Float}
    {grid : Array Cell} (hsize : grid.size = n.toNat * n.toNat) (hlt : grid.size < 2 ^ 64)
    (hA : accepted (reconstructedSweep n axisY trials ratio grid) = true) (c : Fin 4) :
    |sweepResidual n axisY trials ratio grid c| ≤ sweepBound n axisY trials ratio grid c := by
  have hsz := reconstructedSweep_size n axisY trials ratio grid hlt
  unfold sweepResidual sweepBound
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk' := Finset.mem_range.mp hk
  have hcell := reconstructedSweep_cell (axisY := axisY) (trials := trials) (ratio := ratio)
    hsize hlt hk'
  have h0 : (sweepCell n.toNat axisY trials ratio grid (lineOf n.toNat axisY k)
      (positionOf n.toNat axisY k)).status = 0 := by
    rw [← hcell, getElem!_pos _ k (by omega)]
    exact accepted_ok hA (by omega) _ (Array.getElem_mem _)
  have hm : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h | h
    · rw [hsize, h] at hk'; simp at hk'
    · exact h
  have hp : positionOf n.toNat axisY k < n.toNat := by
    simp only [positionOf]
    split
    · exact Nat.div_lt_of_lt_mul (by rw [← hsize]; exact hk')
    · exact Nat.mod_lt _ hm
  obtain ⟨hs, hv⟩ := lineStep_parts hp h0 (axisComponent axisY c)
  have hold : stateAt grid[k]!.state c = stateAt (lineState n.toNat axisY grid
      (lineOf n.toNat axisY k) (positionOf n.toNat axisY k)) (axisComponent axisY c) := by
    rw [lineState, stateAt_oriented, lineIndex_of]
  rw [hcell, stateAt_sweepCell, hv, hold]
  exact update_balance hs

/-! The balance of steps and runs. -/

/-- The flux through the boundary over a step with ratio `r` from `grid`: the x sweep of `grid`
and the y sweep of the grid it produces. -/
noncomputable def stepFlux (n trials : UInt64) (r : Float) (grid : Array Cell) (c : Fin 4) : ℝ :=
  real r * (sweepBoundary n.toNat false trials grid c +
    sweepBoundary n.toNat true trials (reconstructedSweep n false trials r grid) c)

/-- The rounding residual of a step. -/
noncomputable def stepResidual (n trials : UInt64) (r : Float) (grid : Array Cell) (c : Fin 4) :
    ℝ :=
  sweepResidual n false trials r grid c +
    sweepResidual n true trials r (reconstructedSweep n false trials r grid) c

/-- The bound on the rounding residual of a step. -/
noncomputable def stepBound (n trials : UInt64) (r : Float) (grid : Array Cell) (c : Fin 4) : ℝ :=
  sweepBound n false trials r grid c +
    sweepBound n true trials r (reconstructedSweep n false trials r grid) c

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
    have bx := sweep_balance n false trials ratio grid hsize hlt c
    have by' := sweep_balance n true trials ratio (reconstructedSweep n false trials ratio grid)
      (by rw [hmid, hsize]) (by rw [hmid]; exact hlt) c
    have rx := sweep_residual_le hsize hlt hM c
    have ry := sweep_residual_le (by rw [hmid, hsize]) (by rw [hmid]; exact hlt) hA c
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

/-- The sum of a term of each step of a trace. -/
noncomputable def traceSum (term : Float → Array Cell → ℝ) (steps : List (Float × Array Cell)) :
    ℝ :=
  (steps.map fun s => term s.1 s.2).sum

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
