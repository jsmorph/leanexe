import Project.Euler.Enclosure
import Project.EulerReal.Hyperbolicity
import Project.ProofKit.F64DyadicBounds
import Project.ProofKit.F64Convert

/-! Accepted timesteps of the reconstructed solver.  Every cell of the grid that a step starts
from and of the grid it produces is admissible in exact arithmetic, hence hyperbolic, and the
step satisfies the CFL bound: the ratio of the timestep to the cell width, bounded above, times
the signal speed of every cell is at most 1/2. -/

namespace Project.Euler

open LeanExe.Examples.Euler Project.ProofKit
open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096

theorem absBits_of_word {w : UInt64} (hw : w.toNat < 2 ^ 63) : F64Order.absBits w = w := by
  apply UInt64.toNat_inj.mp
  rw [F64Order.absBits, UInt64.toNat_and,
    show (0x7FFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 63 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hw]

theorem value_nonneg_of_word {w : UInt64} (hw : w.toNat < 2 ^ 63) : 0 ≤ value w := by
  rw [F64Adjacent.unsigned_word_value w hw]
  positivity

/-- On words with sign bit 0, word order implies real order. -/
theorem value_le_of_word {a b : UInt64} (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63)
    (h : a ≤ b) : value a ≤ value b := by
  have := F64Order.abs_value_mono a b (by rwa [absBits_of_word ha, absBits_of_word hb])
  rwa [abs_of_nonneg (value_nonneg_of_word ha), abs_of_nonneg (value_nonneg_of_word hb)] at this

/-- The larger of two floats in word order. -/
abbrev wordMax (a b : Float) : Float := if a.toBits ≤ b.toBits then b else a

theorem wordMax_ge {a b : Float} (ha : a.toBits.toNat < 2 ^ 63) (hb : b.toBits.toNat < 2 ^ 63) :
    (wordMax a b).toBits.toNat < 2 ^ 63 ∧ real a ≤ real (wordMax a b) ∧
      real b ≤ real (wordMax a b) := by
  by_cases hle : a.toBits ≤ b.toBits
  · simp only [wordMax, hle, ite_true]
    exact ⟨hb, value_le_of_word ha hb hle, le_rfl⟩
  · simp only [wordMax, hle, ite_false]
    refine ⟨ha, le_rfl, value_le_of_word hb ha ?_⟩
    rw [UInt64.le_iff_toNat_le] at hle ⊢
    omega

theorem real_pos_of_positive {x : Float} (h : 0 < x.toBits ∧ x.toBits < 0x7FF0000000000000) :
    0 < real x :=
  (F64Order.positiveBits_spec x.toBits (by simpa [F64Order.positiveBits] using h)).2

/-- `q` is admissible in exact arithmetic, and `s` bounds its signal speed in both directions. -/
def SpeedBound (q : Conserved) (s : ℝ) : Prop :=
  EulerReal.Admissible (vec q) ∧
    physicalSpeed (real q.density) (real q.mx) (real q.my) (real q.energy) ≤ s ∧
    physicalSpeed (real q.density) (real q.my) (real q.mx) (real q.energy) ≤ s

theorem SpeedBound.mono {q : Conserved} {s t : ℝ} (h : SpeedBound q s) (hst : s ≤ t) :
    SpeedBound q t :=
  ⟨h.1, h.2.1.trans hst, h.2.2.trans hst⟩

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

/-- A cell of a reconstructed sweep with status 0 is admissible in exact arithmetic. -/
theorem reconstructedSweep_admissible {n : UInt64} {axisY : Bool} {trials : UInt64}
    {ratio : Float} {grid : Array Cell} {c : Cell}
    (hc : c ∈ reconstructedSweep n axisY trials ratio grid) (h0 : c.status = 0) :
    EulerReal.Admissible (vec c.state) := by
  unfold reconstructedSweep LeanExe.build at hc
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hc
  dsimp only at h0 ⊢
  have ha := stateGuard_admissible (reconstructedStep_guard h0)
  cases axisY
  · exact ha
  · exact admissible_swap ha

theorem reconstructedStepGrid_admissible {n trials : UInt64} {ratio : Float} {grid : Array Cell}
    (h : accepted (reconstructedStepGrid n trials ratio grid) = true)
    (hSize : grid.size < 2 ^ 64) :
    ∀ c ∈ reconstructedStepGrid n trials ratio grid, EulerReal.Admissible (vec c.state) := by
  have hMiddle := reconstructedSweep_size n false trials ratio grid hSize
  unfold reconstructedStepGrid reconstructedFinish at h ⊢
  split
  · have hTrial := reconstructedSweep_size n true trials ratio
      (reconstructedSweep n false trials ratio grid) (by omega)
    rw [ite_eq_left (by assumption)] at h
    exact fun c hc => reconstructedSweep_admissible hc (accepted_ok h (by omega) c hc)
  · rename_i hA
    rw [ite_eq_right hA] at h
    exact absurd h hA

/-- An accepted cell bound has sign bit 0 and bounds the signal speed in both directions. -/
theorem cellUpper_ge {q : Conserved} (h : (cellUpper q.density q.mx q.my q.energy).status = 0) :
    (cellUpper q.density q.mx q.my q.energy).value.toBits.toNat < 2 ^ 63 ∧
      SpeedBound q (real (cellUpper q.density q.mx q.my q.energy).value) := by
  unfold cellUpper mergeChecked at h ⊢
  dsimp only at h ⊢
  have hc := rejectedChecked_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hx, hy⟩ := hc
  obtain ⟨-, bx⟩ := speedUpper_ge hx
  obtain ⟨-, byy⟩ := speedUpper_ge hy
  obtain ⟨w, hxm, hym⟩ := wordMax_ge (speedUpper_word hx) (speedUpper_word hy)
  exact ⟨w, stateGuard_admissible (speedUpper_guard hx), bx.trans hxm, byy.trans hym⟩

/-- A property of `LeanExe.loop`'s state that holds at index 0, and that each step below `k`
carries from index `i` to `i + 1`, holds at every index up to `k`. -/
theorem loop_inv {P : Nat → α → Prop} {f : UInt64 → α → α} {init : α} {k : Nat}
    (h0 : P 0 init) (hStep : ∀ i < k, ∀ a, P i a → P (i + 1) (f (UInt64.ofNat i) a)) :
    ∀ m ≤ k, P m (Nat.fold m (fun i _ a => f (UInt64.ofNat i) a) init) := by
  intro m hm
  induction m with
  | zero => exact h0
  | succ m ih =>
    rw [Nat.fold_succ]
    exact hStep m (by omega) _ (ih (by omega))

/-- `gridUpper` with its loop's step named. -/
theorem gridUpper_loop (grid : Array Cell) :
    ∃ f : UInt64 → UInt64 × Float → UInt64 × Float,
      (∀ i acc, f i acc =
        (if acc.1 == 0 && (cellUpper grid[i.toNat]!.state.density grid[i.toNat]!.state.mx
            grid[i.toNat]!.state.my grid[i.toNat]!.state.energy).status == 0 then 0 else 1,
          if acc.1 == 0 && (cellUpper grid[i.toNat]!.state.density grid[i.toNat]!.state.mx
              grid[i.toNat]!.state.my grid[i.toNat]!.state.energy).status == 0 then
            wordMax acc.2 (cellUpper grid[i.toNat]!.state.density grid[i.toNat]!.state.mx
              grid[i.toNat]!.state.my grid[i.toNat]!.state.energy).value
          else 0)) ∧
      gridUpper grid =
        match LeanExe.loop grid.size.toUInt64 ((0 : UInt64), (0 : Float)) f with
        | (status, value) => ⟨status, value⟩ :=
  ⟨_, fun _ _ => rfl, rfl⟩

/-- An accepted grid bound has sign bit 0 and bounds the signal speed of every cell. -/
theorem gridUpper_ge {grid : Array Cell} (h : (gridUpper grid).status = 0)
    (hSize : grid.size < 2 ^ 64) :
    (gridUpper grid).value.toBits.toNat < 2 ^ 63 ∧
      ∀ i (hi : i < grid.size), SpeedBound grid[i].state (real (gridUpper grid).value) := by
  have hk : grid.size.toUInt64.toNat = grid.size := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hSize]
  obtain ⟨f, hf, hDef⟩ := gridUpper_loop grid
  have hInv := loop_inv (P := fun m (acc : UInt64 × Float) => acc.1 = 0 →
      acc.2.toBits.toNat < 2 ^ 63 ∧
        ∀ i (hi : i < grid.size), i < m → SpeedBound grid[i].state (real acc.2))
    (f := f) (init := ((0 : UInt64), (0 : Float))) (k := grid.size.toUInt64.toNat)
    (fun _ => ⟨by rw [zero_bits]; decide, fun _ _ hm => absurd hm (Nat.not_lt_zero _)⟩)
    (fun i hi acc hacc => by
      rw [hf]
      have hig : i < grid.size := by omega
      have hi' : (UInt64.ofNat i).toNat = i :=
        UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
      simp only [hi', getElem!_pos grid i hig]
      intro h0
      by_cases hs : acc.1 = 0 ∧
          (cellUpper grid[i].state.density grid[i].state.mx grid[i].state.my
            grid[i].state.energy).status = 0
      · obtain ⟨hs1, hs2⟩ := hs
        simp only [hs1, hs2, beq_self_eq_true, Bool.and_self, ite_true]
        obtain ⟨wa, ba⟩ := hacc hs1
        obtain ⟨wc, bc⟩ := cellUpper_ge hs2
        obtain ⟨w, ham, hcm⟩ := wordMax_ge wa wc
        refine ⟨w, fun j hj hji => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hji | rfl
        · exact (ba j hj hji).mono ham
        · exact bc.mono hcm
      · simp only [Bool.and_eq_true, beq_iff_eq] at h0
        rw [ite_eq_right hs] at h0
        exact absurd h0 (by decide))
    grid.size.toUInt64.toNat le_rfl
  rw [hDef] at h ⊢
  unfold LeanExe.loop at h ⊢
  generalize Nat.fold grid.size.toUInt64.toNat _ ((0 : UInt64), (0 : Float)) = R at h hInv ⊢
  obtain ⟨status, value⟩ := R
  obtain ⟨w, hB⟩ := hInv h
  exact ⟨w, fun i hi => hB i hi (by omega)⟩

/-- Converting a word below `2^53` to binary64 is exact. -/
theorem real_toFloat {n : UInt64} (hn : n.toNat < 2 ^ 53) : real n.toFloat = n.toNat := by
  have hr : CodeLib.IEEE64.roundedMagnitude (n.toNat * 2 ^ 1074) = n.toNat * 2 ^ 1074 := by
    by_cases hz : n.toNat = 0
    · rw [hz, Nat.zero_mul]
      exact CodeLib.IEEE64.roundedMagnitude_eq_self (by norm_num)
    · have hL1 : 2 ^ Nat.log2 n.toNat ≤ n.toNat := Nat.log2_self_le hz
      have hL2 : n.toNat < 2 ^ (Nat.log2 n.toNat + 1) := Nat.lt_log2_self
      have hL : Nat.log2 n.toNat ≤ 52 := by
        by_contra hc
        have : 2 ^ 53 ≤ 2 ^ Nat.log2 n.toNat := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hsplit : n.toNat * 2 ^ 1074 =
          n.toNat * 2 ^ (52 - Nat.log2 n.toNat) * 2 ^ (1022 + Nat.log2 n.toNat) := by
        rw [Nat.mul_assoc, ← pow_add]
        congr 2
        omega
      rw [hsplit]
      apply F64DyadicBounds.roundedMagnitude_shifted
      · calc 2 ^ 52 = 2 ^ Nat.log2 n.toNat * 2 ^ (52 - Nat.log2 n.toNat) := by
              rw [← pow_add]; congr 1; omega
          _ ≤ n.toNat * 2 ^ (52 - Nat.log2 n.toNat) := Nat.mul_le_mul_right _ hL1
      · calc n.toNat * 2 ^ (52 - Nat.log2 n.toNat)
            ≤ 2 ^ (Nat.log2 n.toNat + 1) * 2 ^ (52 - Nat.log2 n.toNat) :=
              Nat.mul_le_mul_right _ hL2.le
          _ = 2 ^ 53 := by rw [← pow_add]; congr 1; omega
  have hv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.convertI64U n) = (n.toNat * 2 ^ 1074 : Nat) := by
    show Wasm.IEEE64.scaledValue
      (Wasm.IEEE64.roundScaledMagnitude false (n.toNat * 2 ^ 1074)) = _
    rw [F64Packing.scaledValue_pack false _ (by
      calc n.toNat * 2 ^ 1074 < 2 ^ 53 * 2 ^ 1074 :=
            Nat.mul_lt_mul_of_pos_right hn (by positivity)
        _ ≤ 2 ^ 2097 := by rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega))]
    simp only [Bool.false_eq_true, ite_false, hr]
  rw [real, F64Convert.toBits_toFloat, value, hv, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, mul_div_assoc, div_self (by positivity), mul_one]

/-- An accepted ratio bounds `dt · n` from above, and its product with `alpha` is at most 1/2. -/
theorem gridRatio_le {n : UInt64} {dt alpha : Float} (h : (gridRatio n dt alpha).status = 0) :
    0 < real dt ∧ 0 < real alpha ∧ real dt * n.toNat ≤ real (gridRatio n dt alpha).value ∧
      real (gridRatio n dt alpha).value * real alpha ≤ 1 / 2 := by
  unfold gridRatio at h ⊢
  dsimp only at h ⊢
  have hc := rejectedChecked_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h2, h800⟩, hsp⟩, hdt⟩, hspp⟩, hal⟩, hr⟩, hco⟩, hle⟩ := hc
  have hn2 : 2 ≤ n.toNat := UInt64.le_iff_toNat_le.mp h2
  have hn800 : n.toNat ≤ 800 := UInt64.le_iff_toNat_le.mp h800
  have hnreal := real_toFloat (n := n) (by omega)
  have bsp := sound_lower' (outDiv_accepted hsp).2.2.2 rfl
  have br := sound_upper' (outDiv_accepted hr).2.2.2 rfl
  have bco := sound_upper' (outMul_accepted hco).2.2 rfl
  have hdt' := real_pos_of_positive hdt
  have hsp' := real_pos_of_positive hspp
  have hal' := real_pos_of_positive hal
  have hcourant := value_le_of_word (b := 0x3FE0000000000000)
    (by have := UInt64.le_iff_toNat_le.mp hle; simp at this; omega) (by decide) hle
  rw [← half_toBits, show value (0.5 : Float).toBits = 1 / 2 from real_half] at hcourant
  have hone : value (1 : Float).toBits = 1 := by
    rw [one_toBits, value, show Wasm.IEEE64.scaledValue 0x3FF0000000000000 = 2 ^ 1074 by
      decide +kernel, Int.cast_pow, Int.cast_ofNat, div_self (by positivity)]
  simp only [real] at *
  rw [hone, hnreal] at bsp
  have hnpos : (0 : ℝ) < n.toNat := by exact_mod_cast (by omega : 0 < n.toNat)
  refine ⟨hdt', hal', ?_, le_trans bco hcourant⟩
  refine le_trans ?_ br
  rw [le_div_iff₀ hsp']
  have : value (outDiv false 1 n.toFloat).value.toBits * n.toNat ≤ 1 := by
    rwa [le_div_iff₀ hnpos] at bsp
  nlinarith

/-- `reconstructedAttempt` returns status 0 only with an accepted grid that
`reconstructedStepGrid` computes with an accepted ratio for its timestep. -/
theorem reconstructedAttempt_ratio {n trials : UInt64} {time alpha : Float} {grid : Array Cell}
    {dt : Float} {old : Array Cell}
    (h : (reconstructedAttempt n trials time alpha grid dt old).1 = 0) :
    (gridRatio n (reconstructedAttempt n trials time alpha grid dt old).2.1 alpha).status = 0 ∧
      (reconstructedAttempt n trials time alpha grid dt old).2.2 = reconstructedStepGrid n trials
        (gridRatio n (reconstructedAttempt n trials time alpha grid dt old).2.1 alpha).value
        grid ∧
      accepted (reconstructedAttempt n trials time alpha grid dt old).2.2 = true := by
  unfold reconstructedAttempt at h ⊢
  dsimp only at h ⊢
  split
  · rename_i hV
    rw [ite_eq_left hV] at h
    split
    · rename_i hR
      rw [ite_eq_left hR] at h
      unfold reconstructedTry at h ⊢
      dsimp only at h ⊢
      split
      · rename_i hA
        exact ⟨by simpa using hR, rfl, hA⟩
      · rename_i hA
        rw [ite_eq_right hA] at h
        simp at h
    · rename_i hR
      rw [ite_eq_right hR] at h
      simp at h
  · rename_i hV
    rw [ite_eq_right hV] at h
    simp at h

theorem reconstructedAdvanceWith_ratio {n trials : UInt64} {time dt alpha : Float}
    {grid : Array Cell} (h : (reconstructedAdvanceWith n trials time dt alpha grid).1 = 0) :
    ∃ dt' : Float, (gridRatio n dt' alpha).status = 0 ∧
      (reconstructedAdvanceWith n trials time dt alpha grid).2.1 = time + dt' ∧
      (reconstructedAdvanceWith n trials time dt alpha grid).2.2 =
        reconstructedStepGrid n trials (gridRatio n dt' alpha).value grid ∧
      accepted (reconstructedAdvanceWith n trials time dt alpha grid).2.2 = true := by
  obtain ⟨cond, step, -, hStepEq, hDef⟩ :=
    reconstructedAdvanceWith_loop n trials time dt alpha grid
  have hInv := repeatWhile_inv (P := fun s : UInt64 × Float × Array Cell => s.1 = 0 →
      (gridRatio n s.2.1 alpha).status = 0 ∧
        s.2.2 = reconstructedStepGrid n trials (gridRatio n s.2.1 alpha).value grid ∧
        accepted s.2.2 = true)
    (cond := cond) (step := step) (x0 := ((9 : UInt64), dt, (#[] : Array Cell))) 2048 (by simp)
    (fun x _ _ hx => by rw [hStepEq] at hx ⊢; exact reconstructedAttempt_ratio hx)
  rw [hDef] at h ⊢
  generalize LeanExe.repeatWhile 2048 ((9 : UInt64), dt, (#[] : Array Cell)) cond step = R
    at h hInv ⊢
  obtain ⟨status, dt', trial⟩ := R
  dsimp only at h hInv ⊢
  split
  · rename_i hS
    obtain ⟨hr, ht, ha⟩ := hInv (by simpa using hS)
    exact ⟨dt', hr, rfl, ht, ha⟩
  · rename_i hS
    rw [ite_eq_right hS] at h
    split at h
    · simp at h
    · simp only at h
      exact absurd (by simp [h]) hS

/-- A timestep that the solver accepted.  It advances the time by some `dt > 0` and updates the
grid with a ratio `r ≥ dt · n`, where `n` is the number of cells per side.  Every cell of the grid
it starts from is admissible in exact arithmetic, and `r` times its signal speed in either
direction is at most 1/2.  Every cell of the grid it produces is admissible. -/
def AcceptedStep (n trials : UInt64) (a b : Float × Array Cell) : Prop :=
  ∃ dt r : Float, 0 < real dt ∧ b.1 = a.1 + dt ∧ b.2 = reconstructedStepGrid n trials r a.2 ∧
    real dt * n.toNat ≤ real r ∧
    (∀ i (hi : i < a.2.size), EulerReal.Admissible (vec a.2[i].state) ∧
      real r * physicalSpeed (real a.2[i].state.density) (real a.2[i].state.mx)
        (real a.2[i].state.my) (real a.2[i].state.energy) ≤ 1 / 2 ∧
      real r * physicalSpeed (real a.2[i].state.density) (real a.2[i].state.my)
        (real a.2[i].state.mx) (real a.2[i].state.energy) ≤ 1 / 2) ∧
    ∀ c ∈ b.2, EulerReal.Admissible (vec c.state)

/-- An accepted reconstructed timestep is an `AcceptedStep`. -/
theorem reconstructedAdvanceStep_accepted {n trials : UInt64} {time : Float} {grid : Array Cell}
    (h : (reconstructedAdvanceStep n trials time grid).1 = 0) (hSize : grid.size < 2 ^ 64) :
    AcceptedStep n trials (time, grid) ((reconstructedAdvanceStep n trials time grid).2.1,
      (reconstructedAdvanceStep n trials time grid).2.2) := by
  unfold AcceptedStep
  unfold reconstructedAdvanceStep at h ⊢
  dsimp only at h ⊢
  split
  · rename_i hS
    rw [ite_eq_left hS] at h
    obtain ⟨-, hB⟩ := gridUpper_ge (by simpa using hS) hSize
    obtain ⟨dt, hR, ht, hg, hA⟩ := reconstructedAdvanceWith_ratio h
    obtain ⟨hdt, -, hdn, hra⟩ := gridRatio_le hR
    refine ⟨dt, _, hdt, ht, hg, hdn, fun i hi => ?_, ?_⟩
    · obtain ⟨hadm, bx, byy⟩ := hB i hi
      have hr0 := le_trans (mul_nonneg hdt.le (Nat.cast_nonneg _)) hdn
      exact ⟨hadm, le_trans (mul_le_mul_of_nonneg_left bx hr0) hra,
        le_trans (mul_le_mul_of_nonneg_left byy hr0) hra⟩
    · rw [hg] at hA ⊢
      exact reconstructedStepGrid_admissible hA hSize
  · rename_i hS
    rw [ite_eq_right hS] at h
    simp at h

/-- Every timestep of a reconstructed run that returns status 0 is an `AcceptedStep`: a chain of
them leads from time 0 and the initial grid to the run's final time and grid. -/
theorem reconstructedRunFrom_steps {n trials : UInt64}
    (h : (reconstructedRunFrom n trials).1 = 0) :
    Relation.ReflTransGen (AcceptedStep n trials) (0, initialCells n)
      ((reconstructedRunFrom n trials).2.1, (reconstructedRunFrom n trials).2.2) := by
  obtain ⟨cond, step, hCondEq, hStepEq, hDef⟩ := reconstructedRunFrom_loop n trials
  have hN : (n * n).toNat < 2 ^ 64 := (n * n).toNat_lt
  have hInv := repeatWhile_inv (P := fun s : UInt64 × Float × Array Cell =>
      s.2.2.size = (n * n).toNat ∧
        (s.1 = 0 → Relation.ReflTransGen (AcceptedStep n trials) (0, initialCells n)
          (s.2.1, s.2.2)))
    (cond := cond) (step := step) (x0 := ((0 : UInt64), (0 : Float), initialCells n))
    4294967296 ⟨initialCells_size n, fun _ => .refl⟩
    (fun x hc hx => by
      rw [hStepEq]
      have hc' : x.1 = 0 := by
        rw [hCondEq] at hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact hc.1
      have hs1 := hx.1
      refine ⟨(reconstructedAdvanceStep_size (by omega)).trans hs1, fun hs => ?_⟩
      exact (hx.2 hc').tail (reconstructedAdvanceStep_accepted hs (by omega)))
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
    exact hInv.2 rfl

theorem reconstructedRun_steps {n trials : UInt64} (h : (reconstructedRun n trials).1 = 0) :
    Relation.ReflTransGen (AcceptedStep n trials) (0, initialCells n)
      ((reconstructedRun n trials).2.1, (reconstructedRun n trials).2.2) := by
  unfold reconstructedRun at h ⊢
  split at h
  · rename_i hn
    rw [ite_eq_left hn]
    exact reconstructedRunFrom_steps h
  · simp at h

/-- The final grid of a reconstructed run that returns status 0 is admissible in exact
arithmetic, and the Euler flux is hyperbolic at each of its states. -/
theorem reconstructedRun_hyperbolic {n trials : UInt64} (h : (reconstructedRun n trials).1 = 0) :
    ∀ c ∈ (reconstructedRun n trials).2.2,
      EulerReal.Admissible (vec c.state) ∧ EulerReal.Hyperbolic (vec c.state) := by
  have hTime := (reconstructedRun_ok h).2.2.1
  rcases Relation.ReflTransGen.cases_tail (reconstructedRun_steps h) with hEq | ⟨a, -, hStep⟩
  · have h0 := congrArg Prod.fst hEq
    dsimp only at h0
    rw [h0] at hTime
    exact absurd hTime (by decide +kernel)
  · obtain ⟨-, -, -, -, -, -, -, hFinal⟩ := hStep
    exact fun c hc => ⟨hFinal c hc, EulerReal.admissible_hyperbolic _ (hFinal c hc)⟩

end Project.Euler
