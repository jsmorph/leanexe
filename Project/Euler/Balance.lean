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

end Project.Euler
