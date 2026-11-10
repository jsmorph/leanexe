import LeanExe.ProofKit.F64SignedRounding
import LeanExe.ProofKit.F64AdjacentSigned
import LeanExe.ProofKit.F64Magnitude

/-!
Real bounds from a count of steps.  A finite word whose position lies above that of the
nearest-even reference of `y` has a value of at least `y`, and one whose position lies below it
has a value of at most `y`.  `nextUp` and `nextDown` move the position of a finite word by one, so
a word within one step of the reference, moved two steps up or down, bounds `y`.
-/

namespace Library.Numerics.Interval.Steps

open CodeLib.IEEE64 LeanExe.ProofKit
open LeanExe.ProofKit.F64SignedRounding (position WithinSteps)
open LeanExe.ProofKit.F64Adjacent (nextUp nextDown)

set_option exponentiation.threshold 4096

/-! ### Nonnegative words -/

theorem upper_of_above (y : ℝ) (u : UInt64) (hu : u.toNat < 0x7FF0000000000000)
    (h : (F64PositiveRounding.roundNearestEven y).toNat < u.toNat) : y ≤ value u := by
  by_cases ht : F64PositiveRounding.overflowThreshold ≤ y
  · rw [F64PositiveRounding.reference_overflow y ht] at h
    have hi : F64PositiveRounding.positiveInfinity.toNat = 0x7FF0000000000000 := by decide
    omega
  · rw [F64PositiveRounding.reference_finite y (lt_of_not_ge ht)] at h
    have hw := (F64NearestEven.roundNearestEven_spec y).1
    by_contra hn
    have hn := not_le.mp hn
    have hlt := F64PositiveOrder.value_strict (show u.toNat < 2 ^ 63 by omega) h
    have hd := hw.2 u hu
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at hd
    linarith

theorem lower_of_below (y : ℝ) (u : UInt64) (hu : u.toNat < 0x7FF0000000000000)
    (h : u.toNat < (F64PositiveRounding.roundNearestEven y).toNat) : value u ≤ y := by
  by_cases ht : F64PositiveRounding.overflowThreshold ≤ y
  · have hm : value u ≤ value (0x7FEFFFFFFFFFFFFF : UInt64) :=
      (F64PositiveOrder.value_le_iff (show u.toNat < 2 ^ 63 by omega) (by decide)).mpr (by
        have hc : (0x7FEFFFFFFFFFFFFF : UInt64).toNat = 0x7FEFFFFFFFFFFFFF := by decide
        omega)
    rw [F64PositiveRounding.largest_finite_value] at hm
    have hc : (2 : ℝ) ^ 1024 - 2 ^ 971 ≤ F64PositiveRounding.overflowThreshold := by
      norm_num [F64PositiveRounding.overflowThreshold]
    linarith
  · rw [F64PositiveRounding.reference_finite y (lt_of_not_ge ht)] at h
    have hw := (F64NearestEven.roundNearestEven_spec y).1
    have hr : (F64NearestEven.roundNearestEven y).toNat < 2 ^ 63 :=
      lt_trans hw.1 (by decide)
    by_contra hn
    have hn := not_le.mp hn
    have hlt := F64PositiveOrder.value_strict hr h
    have hd := hw.2 u hu
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at hd
    linarith

/-! ### Positions of the reference -/

theorem position_reference_nonneg (y : ℝ) (hy : 0 ≤ y) :
    position (F64SignedRounding.roundNearestEven y) =
      ((F64PositiveRounding.roundNearestEven y).toNat : ℤ) := by
  have hr := F64SignedRounding.positive_reference_le y
  simp only [F64SignedRounding.roundNearestEven, hy, ite_true]
  exact F64SignedRounding.position_of_lt _ (by omega)

theorem position_reference_neg (y : ℝ) (hy : y < 0) :
    position (F64SignedRounding.roundNearestEven y) =
      -((F64PositiveRounding.roundNearestEven (-y)).toNat : ℤ) := by
  have hr := F64SignedRounding.positive_reference_le (-y)
  have hn : ¬ 0 ≤ y := not_le.mpr hy
  simp only [F64SignedRounding.roundNearestEven, hn, ite_false,
    F64SignedRounding.position_negate]
  rw [F64SignedRounding.position_of_lt _ (by omega)]

theorem position_reference_negate (y : ℝ) :
    position (F64SignedRounding.roundNearestEven (-y)) =
      -position (F64SignedRounding.roundNearestEven y) := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [position_reference_nonneg (-y) (by linarith), position_reference_neg y hy, neg_neg]
  · subst hy
    rw [neg_zero, position_reference_nonneg 0 le_rfl,
      F64SignedRounding.positive_reference_zero]
    rfl
  · rw [position_reference_neg (-y) (by linarith), position_reference_nonneg y hy.le, neg_neg]

/-! ### Signed words -/

theorem nonneg_value (u : UInt64) (hs : u.toNat < 2 ^ 63) : 0 ≤ value u := by
  rw [F64Adjacent.unsigned_word_value u hs]
  positivity

theorem upper_of_position (y : ℝ) (u : UInt64) (hu : Finite u)
    (h : position (F64SignedRounding.roundNearestEven y) < position u) : y ≤ value u := by
  have hb := F64Adjacent.finite_word_bound u hu
  have hn := u.toNat_lt
  by_cases hs : u.toNat < 2 ^ 63
  · rw [F64SignedRounding.position_of_lt u hs] at h
    rcases le_or_gt 0 y with hy | hy
    · rw [position_reference_nonneg y hy] at h
      exact upper_of_above y u (by omega) (by exact_mod_cast h)
    · exact hy.le.trans (nonneg_value u hs)
  · have hge : 2 ^ 63 ≤ u.toNat := by omega
    have hpos : position u = -((u.toNat - 2 ^ 63 : ℕ) : ℤ) := by
      simp only [position, Wasm.IEEE64.sign, decide_eq_true hge, ite_true]
    have hv : (Wasm.IEEE64.negate u).toNat = u.toNat - 2 ^ 63 := by
      rw [F64SignedRounding.negate_toNat]
      simp only [Wasm.IEEE64.sign, decide_eq_true hge, ite_true]
    obtain ⟨-, hval⟩ := F64Magnitude.negate_value u hu
    rw [hpos] at h
    rcases le_or_gt 0 y with hy | hy
    · rw [position_reference_nonneg y hy] at h
      omega
    · rw [position_reference_neg y hy] at h
      have hl := lower_of_below (-y) (Wasm.IEEE64.negate u) (by omega) (by omega)
      rw [hval] at hl
      linarith

theorem lower_of_position (y : ℝ) (u : UInt64) (hu : Finite u)
    (h : position u < position (F64SignedRounding.roundNearestEven y)) : value u ≤ y := by
  obtain ⟨hf, hval⟩ := F64Magnitude.negate_value u hu
  have hup := upper_of_position (-y) (Wasm.IEEE64.negate u) hf (by
    rw [position_reference_negate, F64SignedRounding.position_negate]
    omega)
  rw [hval] at hup
  linarith

/-! ### Adjacent words -/

theorem position_nextUp (w : UInt64) (hw : Finite w) : position (nextUp w) = position w + 1 := by
  have hb := F64Adjacent.finite_word_bound w hw
  have hn := w.toNat_lt
  by_cases hz : w = 0x8000000000000000
  · subst hz
    decide +kernel
  · have hne : w.toNat ≠ 2 ^ 63 := fun he => hz (UInt64.toNat_inj.mp he)
    by_cases hs : w.toNat < 2 ^ 63
    · have hlt : w < 0x8000000000000000 := UInt64.lt_iff_toNat_lt.mpr hs
      have e : nextUp w = w + 1 := by simp only [nextUp, hz, ite_false, hlt, ite_true]
      have hs1 := F64Adjacent.word_succ_nat w (by omega)
      rw [e, F64SignedRounding.position_of_lt _ (by omega),
        F64SignedRounding.position_of_lt _ hs, hs1]
      push_cast
      ring
    · have hlt : ¬ w < 0x8000000000000000 := fun h => hs (UInt64.lt_iff_toNat_lt.mp h)
      have e : nextUp w = w - 1 := by simp only [nextUp, hz, ite_false, hlt]
      have hp := F64Adjacent.word_pred_nat w (by omega)
      have h1 : 2 ^ 63 ≤ w.toNat := by omega
      have h2 : 2 ^ 63 ≤ w.toNat - 1 := by omega
      rw [e]
      simp only [position, Wasm.IEEE64.sign, hp, decide_eq_true h1, decide_eq_true h2, ite_true]
      omega

theorem position_nextDown (w : UInt64) (hw : Finite w) :
    position (nextDown w) = position w - 1 := by
  have hb := F64Adjacent.finite_word_bound w hw
  have hn := w.toNat_lt
  by_cases hz : w = 0
  · subst hz
    decide +kernel
  · have hne : w.toNat ≠ 0 := fun he => hz (UInt64.toNat_inj.mp he)
    by_cases hs : w.toNat < 2 ^ 63
    · have hlt : w < 0x8000000000000000 := UInt64.lt_iff_toNat_lt.mpr hs
      have e : nextDown w = w - 1 := by simp only [nextDown, hz, ite_false, hlt, ite_true]
      have hp := F64Adjacent.word_pred_nat w (by omega)
      rw [e, F64SignedRounding.position_of_lt _ (by omega),
        F64SignedRounding.position_of_lt _ hs, hp]
      omega
    · have hlt : ¬ w < 0x8000000000000000 := fun h => hs (UInt64.lt_iff_toNat_lt.mp h)
      have e : nextDown w = w + 1 := by simp only [nextDown, hz, ite_false, hlt]
      have hs1 := F64Adjacent.word_succ_nat w (by omega)
      have h1 : 2 ^ 63 ≤ w.toNat := by omega
      have h2 : 2 ^ 63 ≤ w.toNat + 1 := by omega
      rw [e]
      simp only [position, Wasm.IEEE64.sign, hs1, decide_eq_true h1, decide_eq_true h2, ite_true]
      omega

/-! ### Two steps -/

/-- A word within one step of the reference of `y`, moved two steps up, is at least `y`. -/
theorem two_up (y : ℝ) (w : UInt64) (h : WithinSteps 1 y w) (h0 : Finite w)
    (h1 : Finite (nextUp w)) (h2 : Finite (nextUp (nextUp w))) :
    y ≤ value (nextUp (nextUp w)) := by
  have hp := abs_le.mp h.2
  refine upper_of_position y _ h2 ?_
  rw [position_nextUp _ h1, position_nextUp _ h0]
  omega

/-- A word within one step of the reference of `y`, moved two steps down, is at most `y`. -/
theorem two_down (y : ℝ) (w : UInt64) (h : WithinSteps 1 y w) (h0 : Finite w)
    (h1 : Finite (nextDown w)) (h2 : Finite (nextDown (nextDown w))) :
    value (nextDown (nextDown w)) ≤ y := by
  have hp := abs_le.mp h.2
  refine lower_of_position y _ h2 ?_
  rw [position_nextDown _ h1, position_nextDown _ h0]
  omega

#print axioms upper_of_above
#print axioms lower_of_below
#print axioms position_reference_nonneg
#print axioms position_reference_neg
#print axioms position_reference_negate
#print axioms nonneg_value
#print axioms upper_of_position
#print axioms lower_of_position
#print axioms position_nextUp
#print axioms position_nextDown
#print axioms two_up
#print axioms two_down

end Library.Numerics.Interval.Steps
