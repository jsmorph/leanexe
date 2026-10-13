import Verified.Examples.PowLogPoly

/-!
Three rounded combinations of `Pow.powLog` with relative bounds: `lo3 = rlo (ar + arhi)`, the
sum `lo` of five words, and the final pair `y = hi + lo`, `tail = (hi - y) + lo`.  Each bound
is a multiple of the unit roundoff times the magnitudes of the operands, so that it stays
proportional to `|log x|` when that is small.
-/

namespace Verified.Examples.PowLogSums
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- `lo3 = rlo (A + Ah)` with `A + Ah` rounded and the product rounded. -/
theorem lo3_error (rlo a ah : UInt64) (hlf : Finite rlo) (haf : Finite a) (hhf : Finite ah)
    (hl : |value rlo| ≤ 1) (hs : |value a + value ah| ≤ 1) :
    Finite (Wasm.IEEE64.mul rlo (Wasm.IEEE64.add a ah)) ∧
      |value (Wasm.IEEE64.mul rlo (Wasm.IEEE64.add a ah)) - value rlo * (value a + value ah)| ≤
        3 / 2 ^ 53 * (|value rlo| * |value a + value ah|) + multiplicationUnderflowEpsilon := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  obtain ⟨hsf, hse⟩ := F64AddBounds.add_real_relative a ah haf hhf (hs.trans_lt (by norm_num))
  set s := Wasm.IEEE64.add a ah
  have hsb : |value s| ≤ (1 + 1 / 2 ^ 53) * |value a + value ah| := by
    have := abs_sub_abs_le_abs_sub (value s) (value a + value ah)
    rw [hu] at hse
    linarith
  have hprod : |value rlo * value s| ≤ (1 + 1 / 2 ^ 53) * (|value rlo| * |value a + value ah|) := by
    rw [abs_mul]
    calc
      _ ≤ |value rlo| * ((1 + 1 / 2 ^ 53) * |value a + value ah|) :=
        mul_le_mul_of_nonneg_left hsb (abs_nonneg _)
      _ = _ := by ring
  obtain ⟨hpf, hpe⟩ := F64MulBounds.mul_real_mixed rlo s hlf hsf (by
    calc
      _ ≤ (1 + 1 / 2 ^ 53) * (|value rlo| * |value a + value ah|) := hprod
      _ ≤ (1 + 1 / 2 ^ 53) * (1 * 1) := by gcongr
      _ < (2 : ℝ) ^ 1022 := by norm_num)
  refine ⟨hpf, ?_⟩
  have h1 : |value rlo * value s - value rlo * (value a + value ah)| ≤
      |value rlo| * (1 / 2 ^ 53 * |value a + value ah|) := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (by rw [← hu]; exact hse) (abs_nonneg _)
  have h2 := abs_sub_le (value (Wasm.IEEE64.mul rlo s)) (value rlo * value s)
    (value rlo * (value a + value ah))
  have h3 : unitRoundoff64 * |value rlo * value s| ≤
      1 / 2 ^ 53 * ((1 + 1 / 2 ^ 53) * (|value rlo| * |value a + value ah|)) := by
    rw [hu]
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  have h4 := mul_nonneg (abs_nonneg (value rlo)) (abs_nonneg (value a + value ah))
  nlinarith

/-- The sum `(((a1 + a2) + a3) + a4) + a5`, rounded at each step. -/
theorem sum5 (a1 a2 a3 a4 a5 : UInt64) (h1 : Finite a1) (h2 : Finite a2) (h3 : Finite a3)
    (h4 : Finite a4) (h5 : Finite a5)
    (hS : |value a1| + |value a2| + |value a3| + |value a4| + |value a5| ≤ 1) :
    let s := Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add a1 a2) a3) a4) a5
    Finite s ∧
      |value s - (value a1 + value a2 + value a3 + value a4 + value a5)| ≤
        1 / 2 ^ 53 * (5 * |value a1| + 5 * |value a2| + 4 * |value a3| + 3 * |value a4| +
          |value a5|) ∧
      |value s| ≤ (1 + 5 / 2 ^ 53) *
        (|value a1| + |value a2| + |value a3| + |value a4| + |value a5|) := by
  intro s
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  set S := |value a1| + |value a2| + |value a3| + |value a4| + |value a5|
  have hn1 := abs_nonneg (value a1)
  have hn2 := abs_nonneg (value a2)
  have hn3 := abs_nonneg (value a3)
  have hn4 := abs_nonneg (value a4)
  have hn5 := abs_nonneg (value a5)
  -- step 1
  have hb1 : |value a1 + value a2| ≤ |value a1| + |value a2| := abs_add_le _ _
  obtain ⟨f1, e1⟩ := F64AddBounds.add_real_relative a1 a2 h1 h2 (by
    linarith [show (1 : ℝ) < 2 ^ 1023 by norm_num])
  set s1 := Wasm.IEEE64.add a1 a2
  rw [hu] at e1
  have e1' : |value s1 - (value a1 + value a2)| ≤ 1 / 2 ^ 53 * (|value a1| + |value a2|) :=
    e1.trans (mul_le_mul_of_nonneg_left hb1 (by positivity))
  have m1 : |value s1| ≤ (1 + 1 / 2 ^ 53) * (|value a1| + |value a2|) := by
    have := abs_sub_abs_le_abs_sub (value s1) (value a1 + value a2)
    nlinarith
  -- step 2
  have hb2 : |value s1 + value a3| ≤ (1 + 1 / 2 ^ 53) * (|value a1| + |value a2|) + |value a3| :=
    (abs_add_le _ _).trans (by linarith)
  obtain ⟨f2, e2⟩ := F64AddBounds.add_real_relative s1 a3 f1 h3 (by
    linarith [show (2 : ℝ) < 2 ^ 1023 by norm_num])
  set s2 := Wasm.IEEE64.add s1 a3
  rw [hu] at e2
  have e2' := e2.trans (mul_le_mul_of_nonneg_left hb2 (by positivity))
  have m2 : |value s2| ≤ (1 + 1 / 2 ^ 53) * ((1 + 1 / 2 ^ 53) * (|value a1| + |value a2|) +
      |value a3|) := by
    have := abs_sub_abs_le_abs_sub (value s2) (value s1 + value a3)
    nlinarith
  -- step 3
  have hb3 : |value s2 + value a4| ≤ (1 + 1 / 2 ^ 53) * ((1 + 1 / 2 ^ 53) *
      (|value a1| + |value a2|) + |value a3|) + |value a4| :=
    (abs_add_le _ _).trans (by linarith)
  obtain ⟨f3, e3⟩ := F64AddBounds.add_real_relative s2 a4 f2 h4 (by
    linarith [show (4 : ℝ) < 2 ^ 1023 by norm_num])
  set s3 := Wasm.IEEE64.add s2 a4
  rw [hu] at e3
  have e3' := e3.trans (mul_le_mul_of_nonneg_left hb3 (by positivity))
  have m3 : |value s3| ≤ (1 + 1 / 2 ^ 53) * ((1 + 1 / 2 ^ 53) * ((1 + 1 / 2 ^ 53) *
      (|value a1| + |value a2|) + |value a3|) + |value a4|) := by
    have := abs_sub_abs_le_abs_sub (value s3) (value s2 + value a4)
    nlinarith
  -- step 4
  have hb4 : |value s3 + value a5| ≤ (1 + 1 / 2 ^ 53) * ((1 + 1 / 2 ^ 53) * ((1 + 1 / 2 ^ 53) *
      (|value a1| + |value a2|) + |value a3|) + |value a4|) + |value a5| :=
    (abs_add_le _ _).trans (by linarith)
  obtain ⟨f4, e4⟩ := F64AddBounds.add_real_relative s3 a5 f3 h5 (by
    linarith [show (8 : ℝ) < 2 ^ 1023 by norm_num])
  rw [hu] at e4
  have e4' := e4.trans (mul_le_mul_of_nonneg_left hb4 (by positivity))
  have hE : |value s - (value a1 + value a2 + value a3 + value a4 + value a5)| ≤
      1 / 2 ^ 53 * (5 * |value a1| + 5 * |value a2| + 4 * |value a3| + 3 * |value a4| +
        |value a5|) := by
    have := abs_sub_le (value s) (value s3 + value a5)
      (value a1 + value a2 + value a3 + value a4 + value a5)
    have h34 := abs_sub_le (value s3) (value s2 + value a4)
      (value a1 + value a2 + value a3 + value a4)
    have h23 := abs_sub_le (value s2) (value s1 + value a3) (value a1 + value a2 + value a3)
    have hr1 : |value s3 + value a5 - (value a1 + value a2 + value a3 + value a4 + value a5)| =
        |value s3 - (value a1 + value a2 + value a3 + value a4)| := by ring_nf
    have hr2 : |value s2 + value a4 - (value a1 + value a2 + value a3 + value a4)| =
        |value s2 - (value a1 + value a2 + value a3)| := by ring_nf
    have hr3 : |value s1 + value a3 - (value a1 + value a2 + value a3)| =
        |value s1 - (value a1 + value a2)| := by ring_nf
    nlinarith
  refine ⟨f4, hE, ?_⟩
  have := abs_sub_abs_le_abs_sub (value s) (value a1 + value a2 + value a3 + value a4 + value a5)
  have h6 : |value a1 + value a2 + value a3 + value a4 + value a5| ≤ S := by
    have := abs_add_le (value a1 + value a2 + value a3 + value a4) (value a5)
    have := abs_add_le (value a1 + value a2 + value a3) (value a4)
    have := abs_add_le (value a1 + value a2) (value a3)
    linarith
  linarith

/-- `y = hi + lo` and `tail = (hi - y) + lo`. -/
theorem ytail (hi lo : UInt64) (hhf : Finite hi) (hlf : Finite lo)
    (hb : |value hi| + |value lo| ≤ 2 ^ 11) :
    Finite (Wasm.IEEE64.add hi lo) ∧
      Finite (Wasm.IEEE64.add (Wasm.IEEE64.sub hi (Wasm.IEEE64.add hi lo)) lo) ∧
      |value (Wasm.IEEE64.add hi lo) +
          value (Wasm.IEEE64.add (Wasm.IEEE64.sub hi (Wasm.IEEE64.add hi lo)) lo) -
          (value hi + value lo)| ≤
        (1 + 1 / 2 ^ 40) / 2 ^ 53 * |value lo| + 3 / 2 ^ 106 * |value hi + value lo| ∧
      |value (Wasm.IEEE64.add (Wasm.IEEE64.sub hi (Wasm.IEEE64.add hi lo)) lo)| ≤
        2 / 2 ^ 53 * (|value (Wasm.IEEE64.add hi lo)| + |value lo|) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hhl : |value hi + value lo| ≤ 2 ^ 11 := (abs_add_le _ _).trans hb
  obtain ⟨hyf, hye⟩ := F64AddBounds.add_real_relative hi lo hhf hlf (hhl.trans_lt (by norm_num))
  set y := Wasm.IEEE64.add hi lo
  rw [hu] at hye
  have hhy : |value hi - value y| ≤ |value lo| + 1 / 2 ^ 53 * |value hi + value lo| := by
    have := abs_sub_le (value hi) (value hi + value lo) (value y)
    rw [show value hi - (value hi + value lo) = -value lo by ring, abs_neg,
      abs_sub_comm (value hi + value lo)] at this
    linarith
  have hhyb : |value hi - value y| ≤ 2 ^ 12 := by
    have : 1 / 2 ^ 53 * |value hi + value lo| ≤ 1 / 2 ^ 53 * 2 ^ 11 :=
      mul_le_mul_of_nonneg_left hhl (by positivity)
    have : |value lo| ≤ 2 ^ 11 := by linarith [abs_nonneg (value hi)]
    linarith [show (1 : ℝ) / 2 ^ 53 * 2 ^ 11 ≤ 2 ^ 11 by norm_num]
  obtain ⟨hdf, hde⟩ := F64AddBounds.sub_real_relative hi y hhf hyf (hhyb.trans_lt (by norm_num))
  set d := Wasm.IEEE64.sub hi y
  rw [hu] at hde
  have hdl : |value d + value lo| ≤ 1 / 2 ^ 53 * |value hi + value lo| +
      1 / 2 ^ 53 * |value hi - value y| := by
    have := abs_add_le (value d - (value hi - value y)) (value hi - value y + value lo)
    rw [show value d - (value hi - value y) + (value hi - value y + value lo) =
      value d + value lo by ring, show value hi - value y + value lo =
      -(value y - (value hi + value lo)) by ring, abs_neg] at this
    linarith
  have hdlb : |value d + value lo| ≤ 2 ^ 12 := by
    have h1 : 1 / 2 ^ 53 * |value hi + value lo| ≤ 1 / 2 ^ 53 * 2 ^ 11 :=
      mul_le_mul_of_nonneg_left hhl (by positivity)
    have h2 : 1 / 2 ^ 53 * |value hi - value y| ≤ 1 / 2 ^ 53 * 2 ^ 12 :=
      mul_le_mul_of_nonneg_left hhyb (by positivity)
    linarith [show (1 : ℝ) / 2 ^ 53 * 2 ^ 11 + 1 / 2 ^ 53 * 2 ^ 12 ≤ 2 ^ 12 by norm_num]
  obtain ⟨htf, hte⟩ := F64AddBounds.add_real_relative d lo hdf hlf (hdlb.trans_lt (by norm_num))
  rw [hu] at hte
  refine ⟨hyf, htf, ?_, ?_⟩
  · have h1 := abs_add_le (value (Wasm.IEEE64.add d lo) - (value d + value lo))
      (value d - (value hi - value y))
    rw [show value (Wasm.IEEE64.add d lo) - (value d + value lo) + (value d - (value hi - value y)) =
      value y + value (Wasm.IEEE64.add d lo) - (value hi + value lo) by ring] at h1
    have h2 := abs_nonneg (value hi + value lo)
    have h3 := abs_nonneg (value lo)
    have h4 := abs_nonneg (value hi - value y)
    nlinarith
  · have h1 := abs_sub_abs_le_abs_sub (value (Wasm.IEEE64.add d lo)) (value d + value lo)
    have h2 : |value hi + value lo| ≤ |value y| + 1 / 2 ^ 53 * |value hi + value lo| := by
      have := abs_sub_abs_le_abs_sub (value hi + value lo) (value y)
      rw [abs_sub_comm] at this
      linarith
    have h3 := abs_nonneg (value hi + value lo)
    have h4 := abs_nonneg (value lo)
    have h5 := abs_nonneg (value hi - value y)
    nlinarith

#print axioms lo3_error
#print axioms sum5
#print axioms ytail

end Verified.Examples.PowLogSums
