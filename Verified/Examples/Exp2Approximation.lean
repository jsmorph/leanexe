import Verified.Examples.ExpReductionBounds
import LeanExe.ProofKit.PolyBound

/-!
The polynomial of `Exp2.exp2Core`, `C1 r + C2 r ^ 2 + C3 r ^ 3 + C4 r ^ 4 + C5 r ^ 5`, against
`2 ^ r - 1 = exp (r log 2) - 1` on `|r| ≤ 1/256`.  Each coefficient lies near `(log 2) ^ n / n!`,
which the enclosure of `log 2` from `ExpReductionBounds` bounds, and the Taylor remainder of
degree 6 bounds the rest.  The polynomial's error is at most `2 ^ -58`.
-/

namespace Verified.Examples.Exp2Approximation
open CodeLib.IEEE64
open LeanExe.ProofKit PolyBound

set_option exponentiation.threshold 4096

/-- The coefficients of `Exp2.exp2Core`. -/
def c1 : UInt64 := 0x3FE62E42FEFA39EF
def c2 : UInt64 := 0x3FCEBFBDFF82C424
def c3 : UInt64 := 0x3FAC6B08D70CF4B5
def c4 : UInt64 := 0x3F83B2ABD24650CC
def c5 : UInt64 := 0x3F55D7E09B4E3A84

theorem cast_le {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := Rat.cast_le.mpr h

/-- The polynomial with the coefficients' values. -/
noncomputable def polynomial (r : ℝ) : ℝ :=
  value c1 * r + value c2 * r ^ 2 + value c3 * r ^ 3 + value c4 * r ^ 4 + value c5 * r ^ 5

theorem coefficient_finite : Finite c1 ∧ Finite c2 ∧ Finite c3 ∧ Finite c4 ∧ Finite c5 := by
  unfold CodeLib.IEEE64.Finite c1 c2 c3 c4 c5
  decide +kernel

theorem checked_magnitudes :
    0 ≤ ratOfWord c1 ∧ ratOfWord c1 ≤ 7 / 10 ∧ 0 ≤ ratOfWord c2 ∧ ratOfWord c2 ≤ 1 / 4 ∧
    0 ≤ ratOfWord c3 ∧ ratOfWord c3 ≤ 1 / 16 ∧ 0 ≤ ratOfWord c4 ∧ ratOfWord c4 ≤ 1 / 64 ∧
    0 ≤ ratOfWord c5 ∧ ratOfWord c5 ≤ 1 / 512 := by
  unfold c1 c2 c3 c4 c5
  decide +kernel

theorem coefficient_bounds :
    |value c1| ≤ 7 / 10 ∧ |value c2| ≤ 1 / 4 ∧ |value c3| ≤ 1 / 16 ∧ |value c4| ≤ 1 / 64 ∧
      |value c5| ≤ 1 / 512 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5'⟩ := checked_magnitudes
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hl := cast_le h1
    have hu := cast_le h1'
    push_cast at hl hu
    rw [← ratOfWord_cast, abs_of_nonneg hl]
    linarith
  · have hl := cast_le h2
    have hu := cast_le h2'
    push_cast at hl hu
    rw [← ratOfWord_cast, abs_of_nonneg hl]
    linarith
  · have hl := cast_le h3
    have hu := cast_le h3'
    push_cast at hl hu
    rw [← ratOfWord_cast, abs_of_nonneg hl]
    linarith
  · have hl := cast_le h4
    have hu := cast_le h4'
    push_cast at hl hu
    rw [← ratOfWord_cast, abs_of_nonneg hl]
    linarith
  · have hl := cast_le h5
    have hu := cast_le h5'
    push_cast at hl hu
    rw [← ratOfWord_cast, abs_of_nonneg hl]
    linarith

/-- Each coefficient against `(log 2) ^ n / n!`, checked on the endpoints of the enclosure of
`log 2`. -/
theorem checked_coefficients :
    0 ≤ ExpReductionBounds.lowerLogTwo ∧ ExpReductionBounds.upperLogTwo ≤ 7 / 10 ∧
    -(1 / 2 ^ 55 : ℚ) ≤ ratOfWord c1 - ExpReductionBounds.upperLogTwo ∧
    ratOfWord c1 - ExpReductionBounds.lowerLogTwo ≤ 1 / 2 ^ 55 ∧
    -(1 / 2 ^ 46 : ℚ) ≤ ratOfWord c2 - ExpReductionBounds.upperLogTwo ^ 2 / 2 ∧
    ratOfWord c2 - ExpReductionBounds.lowerLogTwo ^ 2 / 2 ≤ 1 / 2 ^ 46 ∧
    -(1 / 2 ^ 37 : ℚ) ≤ ratOfWord c3 - ExpReductionBounds.upperLogTwo ^ 3 / 6 ∧
    ratOfWord c3 - ExpReductionBounds.lowerLogTwo ^ 3 / 6 ≤ 1 / 2 ^ 37 ∧
    -(1 / 2 ^ 28 : ℚ) ≤ ratOfWord c4 - ExpReductionBounds.upperLogTwo ^ 4 / 24 ∧
    ratOfWord c4 - ExpReductionBounds.lowerLogTwo ^ 4 / 24 ≤ 1 / 2 ^ 28 ∧
    -(1 / 2 ^ 22 : ℚ) ≤ ratOfWord c5 - ExpReductionBounds.upperLogTwo ^ 5 / 120 ∧
    ratOfWord c5 - ExpReductionBounds.lowerLogTwo ^ 5 / 120 ≤ 1 / 2 ^ 22 := by
  unfold c1 c2 c3 c4 c5
  decide +kernel

theorem coefficient_errors :
    |value c1 - Real.log 2| ≤ 1 / 2 ^ 55 ∧
    |value c2 - Real.log 2 ^ 2 / 2| ≤ 1 / 2 ^ 46 ∧
    |value c3 - Real.log 2 ^ 3 / 6| ≤ 1 / 2 ^ 37 ∧
    |value c4 - Real.log 2 ^ 4 / 24| ≤ 1 / 2 ^ 28 ∧
    |value c5 - Real.log 2 ^ 5 / 120| ≤ 1 / 2 ^ 22 := by
  obtain ⟨h0, -, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5⟩ := checked_coefficients
  obtain ⟨hl, hh⟩ := ExpReductionBounds.log_two_enclosure
  set lo : ℚ := ExpReductionBounds.lowerLogTwo
  set hi : ℚ := ExpReductionBounds.upperLogTwo
  set L := Real.log 2
  have h0R : (0 : ℝ) ≤ (lo : ℝ) := by simpa using cast_le h0
  have hL0 : 0 ≤ L := h0R.trans hl
  have p (n : Nat) : (lo : ℝ) ^ n ≤ L ^ n ∧ L ^ n ≤ (hi : ℝ) ^ n :=
    ⟨pow_le_pow_left₀ h0R hl n, pow_le_pow_left₀ hL0 hh n⟩
  have a1R := cast_le a1
  have b1R := cast_le b1
  have a2R := cast_le a2
  have b2R := cast_le b2
  have a3R := cast_le a3
  have b3R := cast_le b3
  have a4R := cast_le a4
  have b4R := cast_le b4
  have a5R := cast_le a5
  have b5R := cast_le b5
  push_cast at a1R b1R a2R b2R a3R b3R a4R b4R a5R b5R
  simp only [ratOfWord_cast] at a1R b1R a2R b2R a3R b3R a4R b4R a5R b5R
  have p1 := p 1
  have p2 := p 2
  have p3 := p 3
  have p4 := p 4
  have p5 := p 5
  simp only [pow_one] at p1
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩,
    abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, p5.1, p5.2]

theorem log_two_le : Real.log 2 ≤ 7 / 10 := by
  have h := checked_coefficients.2.1
  have hR := cast_le h
  push_cast at hR
  exact ExpReductionBounds.log_two_enclosure.2.trans hR

/-- The polynomial's error against `2 ^ r - 1`. -/
theorem polynomial_error (r : ℝ) (hr : |r| ≤ 1 / 256) :
    |Real.exp (r * Real.log 2) - 1 - polynomial r| ≤ 1 / 2 ^ 58 := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := coefficient_errors
  set L := Real.log 2
  have hL0 : 0 ≤ L := (ExpReductionBounds.log_two_coarse_bounds.1).trans' (by norm_num)
  have hL1 : L ≤ 7 / 10 := log_two_le
  set y := r * L
  have hy : |y| ≤ 7 / 2560 := by
    rw [abs_mul, abs_of_nonneg hL0]
    calc
      _ ≤ 1 / 256 * (7 / 10) := mul_le_mul hr hL1 hL0 (by norm_num)
      _ = 7 / 2560 := by norm_num
  have hb : |Real.exp y - (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120)| ≤
      |y| ^ 6 * (7 / 4320) := by
    have h := Real.exp_bound (x := y) (hy.trans (by norm_num)) (n := 6) (by norm_num)
    have hs : ∑ i ∈ Finset.range 6, y ^ i / (i.factorial : ℝ) =
        1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
    have hc : ((Nat.succ 6 : Nat) : ℝ) / ((Nat.factorial 6 : Nat) * (6 : Nat)) = 7 / 4320 := by
      norm_num [Nat.factorial]
    rw [hs, hc] at h
    exact h
  have hE : |Real.exp y - (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120)| ≤
      1 / 2 ^ 60 := by
    have hrem : |y| ^ 6 * (7 / 4320) ≤ 1 / 2 ^ 60 := by
      calc
        _ ≤ (7 / 2560 : ℝ) ^ 6 * (7 / 4320) := by gcongr
        _ ≤ 1 / 2 ^ 60 := by norm_num
    exact hb.trans hrem
  have hid : Real.exp y - 1 - polynomial r =
      (Real.exp y - (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120)) -
        ((value c1 - L) * r + (value c2 - L ^ 2 / 2) * r ^ 2 + (value c3 - L ^ 3 / 6) * r ^ 3 +
          (value c4 - L ^ 4 / 24) * r ^ 4 + (value c5 - L ^ 5 / 120) * r ^ 5) := by
    simp only [polynomial, y]
    ring
  have term (d : ℝ) (n : Nat) (δ : ℝ) (hd : |d| ≤ δ) :
      |d * r ^ n| ≤ δ * (1 / 256) ^ n := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hd (pow_le_pow_left₀ (abs_nonneg r) hr n) (by positivity)
      ((abs_nonneg d).trans hd)
  have t1 := term _ 1 _ e1
  have t2 := term _ 2 _ e2
  have t3 := term _ 3 _ e3
  have t4 := term _ 4 _ e4
  have t5 := term _ 5 _ e5
  simp only [pow_one] at t1
  rw [hid]
  calc
    _ ≤ |Real.exp y - (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120)| +
        (|(value c1 - L) * r| + |(value c2 - L ^ 2 / 2) * r ^ 2| +
          |(value c3 - L ^ 3 / 6) * r ^ 3| + |(value c4 - L ^ 4 / 24) * r ^ 4| +
          |(value c5 - L ^ 5 / 120) * r ^ 5|) := by
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      exact abs_add_le _ _
    _ ≤ 1 / 2 ^ 60 + (1 / 2 ^ 55 * (1 / 256) + 1 / 2 ^ 46 * (1 / 256) ^ 2 +
          1 / 2 ^ 37 * (1 / 256) ^ 3 + 1 / 2 ^ 28 * (1 / 256) ^ 4 +
          1 / 2 ^ 22 * (1 / 256) ^ 5) := by
      gcongr
    _ ≤ 1 / 2 ^ 58 := by norm_num

#print axioms coefficient_finite
#print axioms coefficient_bounds
#print axioms coefficient_errors
#print axioms polynomial_error

end Verified.Examples.Exp2Approximation
