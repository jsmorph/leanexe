import Verified.Examples.Exp2Approximation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
The constants of `Exp2.exp10Core` against `log 10`.  `log 10 = 3 log 2 + log (5/4)`, with `log 2`
enclosed by `ExpReductionBounds` and `log (5/4)` by 45 terms of its series, gives an enclosure
of width below `2 ^ -88`.  On it the kernel checks the polynomial coefficients against
`(log 10) ^ n / n!`, the two-part constant `log10 2 / 128`, the reduction constant
`128 / log10 2`, and the overflow and underflow bounds of `Exp2.exp10With`.
-/

namespace Verified.Examples.Exp10Constants
open CodeLib.IEEE64
open LeanExe.ProofKit PolyBound Exp2Approximation

set_option exponentiation.threshold 4096

/-- The coefficients of `Exp2.exp10Core`'s polynomial, `C0` to `C4`. -/
def e1 : UInt64 := 0x40026BB1BBB55516
def e2 : UInt64 := 0x40053524C73CE9FE
def e3 : UInt64 := 0x4000470591CE4B26
def e4 : UInt64 := 0x3FF2BD76577FE684
def e5 : UInt64 := 0x3FE1446EECCD0EFB

/-- `-log10 2 / 128` in two parts, and `128 / log10 2`. -/
def hiWord : UInt64 := 0xBF63441350A00000
def loWord : UInt64 := 0x3D10C0219DC1DA99
def invWord : UInt64 := 0x407A934F0979A371

/-- The overflow bound `0x1.34413509f79ffp8`, the double below it, and the underflow bound. -/
def oflowWord : UInt64 := 0x40734413509F79FF
def belowOflowWord : UInt64 := 0x40734413509F79FE

/-- 45 terms of the series of `-log (5/4)`. -/
def series : ℚ := ∑ i ∈ Finset.range 45, (-1 / 4 : ℚ) ^ (i + 1) / (i + 1)

def remainder : ℚ := (1 / 4) ^ 46 / (3 / 4)

def lowerLogTen : ℚ := 2918873375210475425442079016975 / 2 ^ 100
def upperLogTen : ℚ := 2918873375210475425442079019194 / 2 ^ 100

theorem checked_log_ten :
    lowerLogTen ≤ 3 * ExpReductionBounds.lowerLogTwo - series - remainder ∧
    3 * ExpReductionBounds.upperLogTwo - series + remainder ≤ upperLogTen := by
  decide +kernel

theorem log_five_fourths : |Real.log (5 / 4) + (series : ℝ)| ≤ (remainder : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -1 / 4) (by norm_num) 45
  have hs : ((series : ℚ) : ℝ) = ∑ i ∈ Finset.range 45, (-1 / 4 : ℝ) ^ (i + 1) / (i + 1) := by
    simp only [series, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
      Rat.cast_ofNat, Rat.cast_add, Rat.cast_natCast]
  have hr : ((remainder : ℚ) : ℝ) = |(-1 / 4 : ℝ)| ^ (45 + 1) / (1 - |(-1 / 4 : ℝ)|) := by
    rw [remainder]
    norm_num
  have h54 : (1 : ℝ) - -1 / 4 = 5 / 4 := by norm_num
  rw [h54] at h
  have key : |(series : ℝ) + Real.log (5 / 4)| ≤ (remainder : ℝ) := by
    rw [hs, hr]
    exact h
  rwa [add_comm (series : ℝ)] at key

theorem log_ten_split : Real.log 10 = 3 * Real.log 2 + Real.log (5 / 4) := by
  rw [show (10 : ℝ) = 2 ^ 3 * (5 / 4) by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  norm_num

theorem log_ten_enclosure :
    (lowerLogTen : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ (upperLogTen : ℝ) := by
  obtain ⟨h1, h2⟩ := checked_log_ten
  obtain ⟨hl, hh⟩ := ExpReductionBounds.log_two_enclosure
  have h1R := cast_le h1
  have h2R := cast_le h2
  push_cast at h1R h2R
  have h5 := abs_le.mp log_five_fourths
  rw [log_ten_split]
  constructor <;> linarith [h5.1, h5.2]

theorem coefficient_finite :
    Finite e1 ∧ Finite e2 ∧ Finite e3 ∧ Finite e4 ∧ Finite e5 ∧ Finite hiWord ∧
      Finite loWord ∧ Finite invWord := by
  unfold CodeLib.IEEE64.Finite e1 e2 e3 e4 e5 hiWord loWord invWord
  decide +kernel

theorem checked_magnitudes :
    0 ≤ ratOfWord e1 ∧ ratOfWord e1 ≤ 24 / 10 ∧ 0 ≤ ratOfWord e2 ∧ ratOfWord e2 ≤ 27 / 10 ∧
    0 ≤ ratOfWord e3 ∧ ratOfWord e3 ≤ 21 / 10 ∧ 0 ≤ ratOfWord e4 ∧ ratOfWord e4 ≤ 12 / 10 ∧
    0 ≤ ratOfWord e5 ∧ ratOfWord e5 ≤ 6 / 10 ∧
    -(1 / 400 : ℚ) ≤ ratOfWord hiWord ∧ ratOfWord hiWord ≤ 0 ∧
    0 ≤ ratOfWord loWord ∧ ratOfWord loWord ≤ 1 / 2 ^ 45 ∧
    0 ≤ ratOfWord invWord ∧ ratOfWord invWord ≤ 426 := by
  unfold e1 e2 e3 e4 e5 hiWord loWord invWord
  decide +kernel

theorem coefficient_bounds :
    |value e1| ≤ 24 / 10 ∧ |value e2| ≤ 27 / 10 ∧ |value e3| ≤ 21 / 10 ∧
      |value e4| ≤ 12 / 10 ∧ |value e5| ≤ 6 / 10 ∧ |value hiWord| ≤ 1 / 400 ∧
      |value loWord| ≤ 1 / 2 ^ 45 ∧ |value invWord| ≤ 426 := by
  obtain ⟨a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, a7, b7, a8, b8⟩ := checked_magnitudes
  have r (w : UInt64) (lo hi : ℚ) (hl : lo ≤ ratOfWord w) (hh : ratOfWord w ≤ hi) :
      (lo : ℝ) ≤ value w ∧ value w ≤ hi := by
    rw [← ratOfWord_cast]
    exact ⟨cast_le hl, cast_le hh⟩
  have c1 := r _ _ _ a1 b1
  have c2 := r _ _ _ a2 b2
  have c3 := r _ _ _ a3 b3
  have c4 := r _ _ _ a4 b4
  have c5 := r _ _ _ a5 b5
  have c6 := r _ _ _ a6 b6
  have c7 := r _ _ _ a7 b7
  have c8 := r _ _ _ a8 b8
  push_cast at c1 c2 c3 c4 c5 c6 c7 c8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith

/-- The coefficients against `(log 10) ^ n / n!`, on the endpoints of the enclosure. -/
theorem checked_coefficients :
    0 ≤ lowerLogTen ∧
    -(1 / 2 ^ 51 : ℚ) ≤ ratOfWord e1 - upperLogTen ∧ ratOfWord e1 - lowerLogTen ≤ 1 / 2 ^ 51 ∧
    -(1 / 2 ^ 44 : ℚ) ≤ ratOfWord e2 - upperLogTen ^ 2 / 2 ∧
    ratOfWord e2 - lowerLogTen ^ 2 / 2 ≤ 1 / 2 ^ 44 ∧
    -(1 / 2 ^ 30 : ℚ) ≤ ratOfWord e3 - upperLogTen ^ 3 / 6 ∧
    ratOfWord e3 - lowerLogTen ^ 3 / 6 ≤ 1 / 2 ^ 30 ∧
    -(1 / 2 ^ 21 : ℚ) ≤ ratOfWord e4 - upperLogTen ^ 4 / 24 ∧
    ratOfWord e4 - lowerLogTen ^ 4 / 24 ≤ 1 / 2 ^ 21 ∧
    -(1 / 2 ^ 12 : ℚ) ≤ ratOfWord e5 - upperLogTen ^ 5 / 120 ∧
    ratOfWord e5 - lowerLogTen ^ 5 / 120 ≤ 1 / 2 ^ 12 := by
  unfold e1 e2 e3 e4 e5
  decide +kernel

theorem coefficient_errors :
    |value e1 - Real.log 10| ≤ 1 / 2 ^ 51 ∧
    |value e2 - Real.log 10 ^ 2 / 2| ≤ 1 / 2 ^ 44 ∧
    |value e3 - Real.log 10 ^ 3 / 6| ≤ 1 / 2 ^ 30 ∧
    |value e4 - Real.log 10 ^ 4 / 24| ≤ 1 / 2 ^ 21 ∧
    |value e5 - Real.log 10 ^ 5 / 120| ≤ 1 / 2 ^ 12 := by
  obtain ⟨h0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5⟩ := checked_coefficients
  obtain ⟨hl, hh⟩ := log_ten_enclosure
  set lo : ℚ := lowerLogTen
  set hi : ℚ := upperLogTen
  set L := Real.log 10
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

/-- The reduction constants and the bounds of `exp10With`, checked on the enclosures. -/
theorem checked_reduction :
    -(1 / 2 ^ 85 : ℚ) ≤ ratOfWord hiWord + ratOfWord loWord +
        ExpReductionBounds.lowerLogTwo / (128 * upperLogTen) ∧
    ratOfWord hiWord + ratOfWord loWord + ExpReductionBounds.upperLogTwo / (128 * lowerLogTen) ≤
      1 / 2 ^ 85 ∧
    -(1 / 2 ^ 40 : ℚ) ≤ ratOfWord invWord - 128 * upperLogTen / ExpReductionBounds.lowerLogTwo ∧
    ratOfWord invWord - 128 * lowerLogTen / ExpReductionBounds.upperLogTwo ≤ 1 / 2 ^ 40 ∧
    (1 / 2 + 1 / 2 ^ 34) * ExpReductionBounds.upperLogTwo / (128 * lowerLogTen) ≤ 1 / 850 ∧
    23 / 10 ≤ lowerLogTen ∧ upperLogTen ≤ 233 / 100 ∧
    1024 * ExpReductionBounds.upperLogTwo ≤ ratOfWord oflowWord * lowerLogTen ∧
    ratOfWord belowOflowWord * upperLogTen ≤ 1024 * ExpReductionBounds.lowerLogTwo - 1 / 2 ^ 43 ∧
    1075 * ExpReductionBounds.upperLogTwo ≤ 350 * lowerLogTen := by
  unfold hiWord loWord invWord oflowWord belowOflowWord
  decide +kernel

#print axioms checked_log_ten
#print axioms log_ten_enclosure
#print axioms coefficient_bounds
#print axioms coefficient_errors
#print axioms checked_reduction

end Verified.Examples.Exp10Constants
