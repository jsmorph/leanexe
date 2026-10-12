import Verified.Examples.AtanTwoQuot
import Verified.Examples.AtanTheoremSmall
import LeanExe.ProofKit.F64TwoSteps
import LeanExe.ProofKit.F64HalfUlp

/-!
Error bounds for the general branch of `Atan.atan2`.  `q` is the rounded quotient `|y/x|` and `Q`
the exact one, with `|q - Q| ≤ 2 ^ -53 Q + 2 ^ -1075`.  `sens` bounds the change of `arctan`
between them by that error over `1 + q Q`, and `sens_range` and `sens_sharp` evaluate the bound
over a range of `q`.  `Good z Q` states that `z` is finite, within `1.49` spacings of `[1, 2)` of
`arctan Q`, and within two steps of it.  For `x < 0` the code returns `π - (z - πlo)` or
`(z - πlo) - π`, and `neg_finish` turns the first part of `Good` into two steps: the rounding of
`z - πlo` adds at most half a spacing, and the last difference rounds to a nearest word.
-/

namespace Verified.Examples.AtanTwoErr
open CodeLib.IEEE64 LeanExe.ProofKit AtanTwoBranches

set_option exponentiation.threshold 4096

def Good (z : Float) (Q : ℝ) : Prop :=
  Finite z.toBits ∧ |value z.toBits - Real.arctan Q| ≤ 149 / 100 / 2 ^ 52 ∧
    F64SignedRounding.WithinSteps 2 (Real.arctan Q) z.toBits

theorem nonneg_of_sign (w : UInt64) (hs : Wasm.IEEE64.sign w = false) : 0 ≤ value w := by
  rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude w) with h0 | h0
  · have : value w = 0 := by
      simp only [value, Wasm.IEEE64.scaledValue, h0]
      split <;> simp
    rw [this]
  · by_contra hn
    have := (F64Magnitude.sign_value w h0).mpr (lt_of_not_ge hn)
    rw [hs] at this
    exact Bool.false_ne_true this

theorem q_bounds (v Q : ℝ) (h : |v - Q| ≤ Q / 2 ^ 53 + 1 / 2 ^ 1075) :
    Q * (1 - 1 / 2 ^ 53) ≤ v + 1 / 2 ^ 1075 ∧ v ≤ Q * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 := by
  have h' := abs_le.mp h
  constructor <;> linarith [h'.1, h'.2]

theorem arctan_sub_eq (a b : ℝ) (h : 0 ≤ a * b) :
    Real.arctan b - Real.arctan a = Real.arctan ((b - a) / (1 + a * b)) := by
  have hsum := Real.arctan_add (x := b) (y := -a) (by nlinarith)
  rw [Real.arctan_neg, ← sub_eq_add_neg] at hsum
  rw [hsum, show (b + -a) / (1 - b * -a) = (b - a) / (1 + a * b) by ring]

theorem sens (q Q e : ℝ) (hq : 0 ≤ q) (hQ : 0 ≤ Q) (h : |q - Q| ≤ e) :
    |Real.arctan q - Real.arctan Q| ≤ e / (1 + q * Q) := by
  have hd : 0 < 1 + q * Q := by nlinarith [mul_nonneg hq hQ]
  rw [abs_sub_comm, arctan_sub_eq q Q (mul_nonneg hq hQ)]
  refine (AtanTheoremConst.abs_arctan_le _).trans ?_
  rw [abs_div, abs_of_pos hd, abs_sub_comm]
  exact div_le_div_of_nonneg_right h hd.le

theorem sens_crude (q Q : ℝ) (hq : 0 ≤ q) (hQ : 0 ≤ Q) (h : |q - Q| ≤ Q / 2 ^ 53 + 1 / 2 ^ 1075) :
    |Real.arctan q - Real.arctan Q| ≤ Q / 2 ^ 53 + 1 / 2 ^ 1075 := by
  refine (sens q Q _ hq hQ h).trans ?_
  exact div_le_self (by positivity) (by nlinarith [mul_nonneg hq hQ])

/-- For `L ≤ q` and `Q ≤ H`, `arctan` moves by at most `H/(1 + L H)` times `2 ^ -53`, plus the
underflow term. -/
theorem sens_range (q Q L H : ℝ) (hL0 : 0 ≤ L) (hL : L ≤ q) (hQ0 : 0 ≤ Q) (hQH : Q ≤ H)
    (h : |q - Q| ≤ Q / 2 ^ 53 + 1 / 2 ^ 1075) :
    |Real.arctan q - Real.arctan Q| ≤ H / (1 + L * H) / 2 ^ 53 + 1 / 2 ^ 1075 := by
  have hq0 : 0 ≤ q := hL0.trans hL
  have hd : 1 ≤ 1 + q * Q := by nlinarith [mul_nonneg hq0 hQ0]
  have hdLH : 0 < 1 + L * H := by nlinarith [mul_nonneg hL0 (hQ0.trans hQH)]
  refine (sens q Q _ hq0 hQ0 h).trans ?_
  rw [add_div]
  apply add_le_add
  · rw [div_div, div_div, div_le_div_iff₀ (mul_pos (by positivity) (by linarith))
      (mul_pos hdLH (by positivity))]
    have h1 : Q * (1 + L * H) ≤ H * (1 + q * Q) := by
      nlinarith [mul_le_mul_of_nonneg_left hL (mul_nonneg hQ0 (hQ0.trans hQH))]
    nlinarith [h1]
  · exact div_le_self (by positivity) hd

/-- For `q ≥ L ≥ 1`, `Q/(1 + q Q) ≤ c` when `c (1 + L²)` exceeds `L` by the error terms, which
holds for `c` just above `L/(1 + L²)`. -/
theorem sens_sharp (q Q L c : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ q) (hQ0 : 0 ≤ Q)
    (h : |q - Q| ≤ Q / 2 ^ 53 + 1 / 2 ^ 1075)
    (hc : L + c / 2 ^ 53 + 1 / 2 ^ 1075 ≤ c * (1 + L ^ 2)) (hc2 : 1 ≤ 2 * c * L) :
    |Real.arctan q - Real.arctan Q| ≤ c / 2 ^ 53 + 1 / 2 ^ 1075 := by
  have hq0 : 0 ≤ q := by linarith
  have hd : 1 ≤ 1 + q * Q := by nlinarith [mul_nonneg hq0 hQ0]
  have hc0 : 0 < c := by nlinarith
  have hQq := (q_bounds q Q h).1
  have key : Q * (1 - c * q) ≤ c := by
    rcases le_or_gt (1 - c * q) 0 with hn | hp
    · nlinarith [mul_le_mul_of_nonneg_left hn hQ0]
    · have h1 : Q * (1 - 1 / 2 ^ 53) * (1 - c * q) ≤ (q + 1 / 2 ^ 1075) * (1 - c * q) :=
        mul_le_mul_of_nonneg_right hQq hp.le
      have h2 : 0 ≤ (q - L) * (c * (q + L) - 1) :=
        mul_nonneg (by linarith) (by nlinarith [mul_le_mul_of_nonneg_left hL hc0.le])
      have h3 : 0 ≤ c * q := mul_nonneg hc0.le hq0
      have h4 : (q + 1 / 2 ^ 1075) * (1 - c * q) ≤ c * (1 - 1 / 2 ^ 53) := by nlinarith
      have h5 : Q * (1 - c * q) * (1 - 1 / 2 ^ 53) ≤ c * (1 - 1 / 2 ^ 53) := by nlinarith
      exact le_of_mul_le_mul_right h5 (by norm_num)
  refine (sens q Q _ hq0 hQ0 h).trans ?_
  rw [add_div]
  apply add_le_add
  · rw [div_div, div_le_div_iff₀ (mul_pos (by positivity) (by linarith)) (by positivity)]
    nlinarith [key]
  · exact div_le_self (by positivity) hd

theorem pi_word : value piF.toBits = 884279719003555 / 2 ^ 48 := by
  rw [piF, F64Bits.toBits_ofBits, if_neg (by decide),
    AtanTheoremCases.word_eq 0x400921FB54442D18 (884279719003555 / 2 ^ 48) (by decide +kernel)]
  norm_num

theorem pilo_word : value piLoF.toBits = 4967757600021511 / 2 ^ 105 := by
  rw [piLoF, F64Bits.toBits_ofBits, if_neg (by decide),
    AtanTheoremCases.word_eq 0x3CA1A62633145C07 (4967757600021511 / 2 ^ 105) (by decide +kernel)]
  norm_num

/-- The results of the quadrants `x < 0` from an angle `z` within `1.49` spacings of `[1, 2)` of
`A ∈ [0, π/2]`. -/
theorem neg_finish (z : Float) (hzf : Finite z.toBits) (A D : ℝ) (hA0 : 0 ≤ A)
    (hA : A ≤ Real.pi / 2) (hz : |value z.toBits - A| ≤ D) (hD : D ≤ 149 / 100 / 2 ^ 52) :
    F64SignedRounding.WithinSteps 2 (Real.pi - A) (piF - (z - piLoF)).toBits ∧
      F64SignedRounding.WithinSteps 2 (A - Real.pi) ((z - piLoF) - piF).toBits := by
  have hp := AtanTheoremConst.pi_close
  rw [abs_le] at hp
  have hvp := pi_word
  have hvl := pilo_word
  have hpf : Finite piF.toBits := by
    rw [piF, F64Bits.toBits_ofBits]
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  have hlf : Finite piLoF.toBits := by
    rw [piLoF, F64Bits.toBits_ofBits]
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  have hz' := abs_le.mp hz
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hz
  have h2 : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
  obtain ⟨hwf, hwe⟩ := F64HalfUlp.sub_half z.toBits piLoF.toBits hzf hlf 1022 (by norm_num) (by
    rw [hvl, h2, abs_lt]
    constructor <;> linarith [hz'.1, hz'.2, hp.1, hp.2])
  rw [← F64Bits.toBits_sub] at hwf hwe
  have h53 : (2 : ℝ) ^ 1022 / 2 / 2 ^ 1074 = 1 / 2 ^ 53 := by norm_num
  rw [h53, hvl] at hwe
  set w := z - piLoF with hw
  have hwe' := abs_le.mp hwe
  have hS1 : 1 ≤ value piF.toBits - value w.toBits := by
    rw [hvp]
    linarith [hz'.1, hz'.2, hp.1, hp.2, hwe'.1, hwe'.2]
  have hy1 : 1 ≤ Real.pi - A := by linarith [hp.1, hp.2]
  have hSy : |(value piF.toBits - value w.toBits) - (Real.pi - A)| < 2 / 2 ^ 52 := by
    rw [hvp, abs_lt]
    constructor <;> linarith [hz'.1, hz'.2, hp.1, hp.2, hwe'.1, hwe'.2]
  have hB : value (UInt64.ofNat (1023 * 2 ^ 52)) = 1 := by
    rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]
    norm_num
  have hsp : (2 : ℝ) * ((2 : ℝ) ^ (1023 - 1) / 2 ^ 1074) = 2 / 2 ^ 52 := by norm_num
  have hSt : |value piF.toBits - value w.toBits| < 2 ^ 1023 := by
    rw [abs_of_pos (by linarith)]
    rw [hvp]
    linarith [hz'.1, hz'.2, hp.1, hp.2, hwe'.1, hwe'.2]
  have hyt : |Real.pi - A| < 2 ^ 1023 := by
    rw [abs_of_pos (by linarith)]
    linarith [hp.2]
  constructor
  · have hc := F64RoundNearest.sub_rounded piF.toBits w.toBits hpf hwf (ne_of_gt (by linarith))
      hSt
    rw [← F64Bits.toBits_sub] at hc
    exact F64TwoSteps.within_two_of_rounded _ _ _ hc 1023 (by norm_num) (by norm_num)
      (by rw [hB, abs_of_pos (by linarith)]; exact hS1)
      (by rw [hB, abs_of_pos (by linarith)]; exact hy1) (by rw [hsp]; exact hSy) hyt
  · have hc := F64RoundNearest.sub_rounded w.toBits piF.toBits hwf hpf (ne_of_lt (by linarith))
      (by rw [abs_sub_comm]; exact hSt)
    rw [← F64Bits.toBits_sub] at hc
    have hSy' : |(value w.toBits - value piF.toBits) - (A - Real.pi)| < 2 / 2 ^ 52 := by
      rw [show value w.toBits - value piF.toBits - (A - Real.pi) =
        -((value piF.toBits - value w.toBits) - (Real.pi - A)) by ring, abs_neg]
      exact hSy
    exact F64TwoSteps.within_two_of_rounded _ _ _ hc 1023 (by norm_num) (by norm_num)
      (by rw [hB, abs_sub_comm, abs_of_pos (by linarith)]; exact hS1)
      (by rw [hB, abs_sub_comm, abs_of_pos (by linarith)]; exact hy1) (by rw [hsp]; exact hSy')
      (by rw [abs_sub_comm]; exact hyt)

/-- A branch of `atan` with an error `E` around `arctan q`, a sensitivity `s`, and room for both
below binade `n`. -/
theorem finish_case (z : Float) (v Q E s : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hn : n < 2046)
    (hzf : Finite z.toBits) (hE : |value z.toBits - Real.arctan v| ≤ E)
    (hs : |Real.arctan v - Real.arctan Q| ≤ s) (hs1 : s ≤ 1 / 2 ^ 53)
    (hB : value (UInt64.ofNat (n * 2 ^ 52)) + E + 1 / 2 ^ 52 ≤ Real.arctan v)
    (hEs : E + s < 5 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074) / 2) (hD : E + s ≤ 149 / 100 / 2 ^ 52) :
    Good z Q := by
  have htot : |value z.toBits - Real.arctan Q| ≤ E + s := by
    have := abs_sub_le (value z.toBits) (Real.arctan v) (Real.arctan Q)
    linarith
  have hs' := (abs_le.mp hs).2
  refine ⟨hzf, htot.trans hD, F64TwoSteps.within_two_of_error _ _ n hn1 hn (E + s) hzf htot ?_ hEs⟩
  generalize value (UInt64.ofNat (n * 2 ^ 52)) = B at hB ⊢
  linarith

#print axioms sens_range
#print axioms sens_sharp
#print axioms neg_finish
#print axioms finish_case

end Verified.Examples.AtanTwoErr
