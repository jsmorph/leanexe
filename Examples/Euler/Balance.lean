import Examples.Euler.ReconstructedProgram
import Examples.Euler.RealState
import LeanExe.ProofKit.F64AddEnclosure
import LeanExe.ProofKit.F64MulEnclosure
import LeanExe.ProofKit.F64AdjacentSigned

/-! Conservation balance of a sweep.  A sweep updates each component of a cell by
`u' = u - r (F_right - F_left)` in three rounded operations, and the two cells beside a face
compute its flux from the same states, so the computed fluxes telescope along a line.  The
residual of a cell, the difference between `u'` and the exact value of the formula on the
computed words, is bounded by the gaps between the neighbors of the three rounded words. -/

namespace Examples.Euler

open Examples.Euler LeanExe.ProofKit
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

/-- The cell that a sweep along an axis makes from an update: a y sweep exchanges the momenta
back. -/
def cellOf (axisY : Bool) (out : Updated) : Cell :=
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

theorem sweep_index {n : UInt64} {axisY : Bool} {k : Nat} (hk : k < n.toNat * n.toNat)
    (hlt : n.toNat * n.toNat < 2 ^ 64) :
    (if axisY = true then UInt64.ofNat k / n else UInt64.ofNat k % n).toNat =
        positionOf n.toNat axisY k ∧
      (if axisY = true then n else 1).toNat = (if axisY then n.toNat else 1) ∧
      (UInt64.ofNat k).toNat =
        (if axisY then lineOf n.toNat axisY k else lineOf n.toNat axisY k * n.toNat) +
          positionOf n.toNat axisY k * (if axisY then n.toNat else 1) ∧
      (if axisY then lineOf n.toNat axisY k else lineOf n.toNat axisY k * n.toNat) +
          (n.toNat - 1) * (if axisY then n.toNat else 1) < 2 ^ 64 ∧
      positionOf n.toNat axisY k < n.toNat := by
  have hm : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h | h
    · rw [h] at hk; simp at hk
    · exact h
  have hK : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  set m := n.toNat with hmdef
  set l := lineOf m axisY k
  set p := positionOf m axisY k
  have hp : p < m := by
    simp only [p, positionOf]
    split
    · exact Nat.div_lt_of_lt_mul hk
    · exact Nat.mod_lt _ hm
  have hl : l < m := by
    simp only [l, lineOf]
    split
    · exact Nat.mod_lt _ hm
    · exact Nat.div_lt_of_lt_mul hk
  refine ⟨?_, ?_, ?_, ?_, hp⟩
  · simp only [p, positionOf]
    split <;> simp [UInt64.toNat_div, UInt64.toNat_mod, hK, ← hmdef]
  · split <;> simp [← hmdef]
  · rw [hK]
    exact (lineIndex_of m axisY k).symm
  · have : (if axisY then l else l * m) + (m - 1) * (if axisY then m else 1) < m * m := by
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

/-- The component along the axis that holds component `c` of a state: a y sweep exchanges the
momenta. -/
def axisComponent (axisY : Bool) (c : Fin 4) : Fin 4 := if axisY then ![0, 2, 1, 3] c else c

theorem stateAt_oriented (axisY : Bool) (q : Conserved) (c : Fin 4) :
    stateAt (oriented axisY q) (axisComponent axisY c) = stateAt q c := by
  cases axisY <;> fin_cases c <;> rfl

theorem stateAt_cellOf (axisY : Bool) (out : Updated) (c : Fin 4) :
    stateAt (cellOf axisY out).state c = updatedAt out (axisComponent axisY c) := by
  cases axisY <;> fin_cases c <;> rfl

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

/-- The flux through the last face of each line minus the flux through its first face, summed
over the lines, where `face l j` is the flux at face `j` of line `l`, between positions `j - 1`
and `j`. -/
noncomputable def boundary (m : Nat) (axisY : Bool) (face : Nat → Nat → Flux) (c : Fin 4) : ℝ :=
  ∑ l ∈ Finset.range m, (real (fluxAt (face l m) (axisComponent axisY c)) -
    real (fluxAt (face l 0) (axisComponent axisY c)))

/-- The flux at the right face of the cell at index `k` minus the flux at its left face. -/
noncomputable def faceDifference (m : Nat) (axisY : Bool) (face : Nat → Nat → Flux) (c : Fin 4)
    (k : Nat) : ℝ :=
  real (fluxAt (face (lineOf m axisY k) (positionOf m axisY k + 1)) (axisComponent axisY c)) -
    real (fluxAt (face (lineOf m axisY k) (positionOf m axisY k)) (axisComponent axisY c))

/-- The rounding residual of a sweep from `before` to `after`: over the cells, the new component
minus the exact value of `u - r (F_right - F_left)` on the computed words. -/
noncomputable def residual (m : Nat) (axisY : Bool) (ratio : Float) (face : Nat → Nat → Flux)
    (before after : Array Cell) (c : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range before.size, (real (stateAt after[k]!.state c) -
    (real (stateAt before[k]!.state c) - real ratio * faceDifference m axisY face c k))

/-- The bound on the rounding residual of a sweep. -/
noncomputable def residualBound (m : Nat) (axisY : Bool) (ratio : Float)
    (face : Nat → Nat → Flux) (before : Array Cell) (c : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range before.size, updateBound ratio (stateAt before[k]!.state c)
    (fluxAt (face (lineOf m axisY k) (positionOf m axisY k)) (axisComponent axisY c))
    (fluxAt (face (lineOf m axisY k) (positionOf m axisY k + 1)) (axisComponent axisY c))

/-- The total of a component after a sweep is the total before, minus the ratio times the flux
through the ends of the lines, plus the rounding residual. -/
theorem balance_identity {m : Nat} {axisY : Bool} {ratio : Float} {face : Nat → Nat → Flux}
    {before after : Array Cell} (hsize : before.size = m * m) (hafter : after.size = before.size)
    (c : Fin 4) :
    total after c = total before c - real ratio * boundary m axisY face c +
      residual m axisY ratio face before after c := by
  have htel : ∑ k ∈ Finset.range before.size, faceDifference m axisY face c k =
      boundary m axisY face c := by
    rw [hsize]
    unfold faceDifference
    rw [sum_lines m axisY (fun l q => real (fluxAt (face l (q + 1)) (axisComponent axisY c)) -
      real (fluxAt (face l q) (axisComponent axisY c)))]
    unfold boundary
    apply Finset.sum_congr rfl
    intro l _
    exact Finset.sum_range_sub (fun q => real (fluxAt (face l q) (axisComponent axisY c))) m
  unfold total residual
  rw [hafter, ← htel, Finset.mul_sum]
  simp only [Finset.sum_sub_distrib]
  ring

/-- When every cell of `after` is the accepted update of the cell of `before` with the fluxes at
its faces, the rounding residual of the sweep is at most `residualBound` in magnitude. -/
theorem residual_le {m : Nat} {axisY : Bool} {ratio : Float} {face : Nat → Nat → Flux}
    {before after : Array Cell}
    (hcell : ∀ k < before.size, ∀ c : Fin 4,
      (update ratio (stateAt before[k]!.state c)
          (fluxAt (face (lineOf m axisY k) (positionOf m axisY k)) (axisComponent axisY c))
          (fluxAt (face (lineOf m axisY k) (positionOf m axisY k + 1))
            (axisComponent axisY c))).status = 0 ∧
        stateAt after[k]!.state c =
          (update ratio (stateAt before[k]!.state c)
            (fluxAt (face (lineOf m axisY k) (positionOf m axisY k)) (axisComponent axisY c))
            (fluxAt (face (lineOf m axisY k) (positionOf m axisY k + 1))
              (axisComponent axisY c))).value)
    (c : Fin 4) :
    |residual m axisY ratio face before after c| ≤ residualBound m axisY ratio face before c := by
  unfold residual residualBound
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  obtain ⟨hs, hv⟩ := hcell k (Finset.mem_range.mp hk) c
  rw [hv]
  exact update_balance hs

/-- The sum of a term of each step of a trace. -/
noncomputable def traceSum (term : Float → Array Cell → ℝ) (steps : List (Float × Array Cell)) :
    ℝ :=
  (steps.map fun s => term s.1 s.2).sum

/-- A chain of steps, each from `b` to `b'` with a ratio `r` for which `S b b' r` holds, with the
ratio and the starting grid of each step. -/
inductive Trace (S : Float × Array Cell → Float × Array Cell → Float → Prop) :
    Float × Array Cell → Float × Array Cell → List (Float × Array Cell) → Prop
  | refl (a : Float × Array Cell) : Trace S a a []
  | tail {a b b' : Float × Array Cell} {steps : List (Float × Array Cell)} (r : Float) :
      Trace S a b steps → S b b' r → Trace S a b' (steps ++ [(r, b.2)])

theorem trace_of_chain {T : Float × Array Cell → Float × Array Cell → Prop}
    {S : Float × Array Cell → Float × Array Cell → Float → Prop}
    (hT : ∀ a b, T a b → ∃ r, S a b r) {a b : Float × Array Cell}
    (h : Relation.ReflTransGen T a b) : ∃ steps, Trace S a b steps := by
  induction h with
  | refl => exact ⟨[], .refl _⟩
  | tail _ hs ih =>
    obtain ⟨steps, ht⟩ := ih
    obtain ⟨r, hr⟩ := hT _ _ hs
    exact ⟨_, .tail r ht hr⟩

/-- When each step changes the total of every component by minus `F` plus a residual `R` of at
most `E`, a trace changes it by minus the sum of `F` plus the sum of `R`, which is at most the sum
of `E`. -/
theorem Trace.balance {S : Float × Array Cell → Float × Array Cell → Float → Prop}
    {F R E : Float → Array Cell → Fin 4 → ℝ}
    (hS : ∀ b b' r, S b b' r → ∀ c, total b'.2 c = total b.2 c - F r b.2 c + R r b.2 c ∧
      |R r b.2 c| ≤ E r b.2 c)
    {a b : Float × Array Cell} {steps : List (Float × Array Cell)} (h : Trace S a b steps)
    (c : Fin 4) :
    total b.2 c = total a.2 c - traceSum (fun r g => F r g c) steps +
        traceSum (fun r g => R r g c) steps ∧
      |traceSum (fun r g => R r g c) steps| ≤ traceSum (fun r g => E r g c) steps := by
  induction h with
  | refl => simp [traceSum]
  | tail r _ hs ih =>
    obtain ⟨hb, hr⟩ := hS _ _ r hs c
    obtain ⟨ihb, ihr⟩ := ih
    simp only [traceSum, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] at ihb ihr ⊢
    refine ⟨?_, ?_⟩
    · rw [hb, ihb]
      ring
    · exact (abs_add_le _ _).trans (add_le_add ihr hr)

end Examples.Euler
