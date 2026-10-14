import Verified.Examples.LgammaAccRefl

/-!
The renormalization at the end of the main branch of `Lgamma.accurate`: four `fastTwoSum` that
turn the triple `a + b + c` into a pair, and the adjustment of the low part by
`1 + copysign (2^-26, fl) copysign (2^-26, fll) = 1 ± 2^-52` when `fh + 2 fl` is exact.  Near the
zeros of `log Γ` the high part of the triple can be smaller than its low part, so the theorem uses
`TgammaAcc2.fts_approx`, which needs no order between the operands: the pair is within
`(B + C)/2^52 + (|a| + B + C)/2^99` of the triple for `|b| ≤ B` and `|c| ≤ C` (`norm_spec`).
The theorem takes the intermediate results of the code as variables with their equations.
-/

namespace Verified.Examples.LgammaAccNorm
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD LgammaAccLow LgammaAccAdd

set_option exponentiation.threshold 4096

/-- The factor `1 ± 2^-52` of the adjustment, with `2^-26` twice. -/
theorem factor26 (a b : Float) :
    Finite (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) a *
        Lgamma.copySign (Float.ofBits 0x3E50000000000000) b).toBits ∧
      |value (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) a *
        Lgamma.copySign (Float.ofBits 0x3E50000000000000) b).toBits - 1| ≤ 1 / 2 ^ 52 := by
  have hw : (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) a *
        Lgamma.copySign (Float.ofBits 0x3E50000000000000) b).toBits = 0x3FF0000000000001 ∨
      (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) a *
        Lgamma.copySign (Float.ofBits 0x3E50000000000000) b).toBits = 0x3FEFFFFFFFFFFFFE := by
    rcases sign_word a.toBits with ha | ha <;> rcases sign_word b.toBits with hb | hb <;>
    · simp only [Lgamma.copySign, F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_ofBits,
        ha, hb, show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
      first
        | exact Or.inl (by decide +kernel)
        | exact Or.inr (by decide +kernel)
  rcases hw with hw | hw <;> rw [hw]
  · refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
    rw [← PolyBound.ratOfWord_cast,
      show PolyBound.ratOfWord 0x3FF0000000000001 = 1 + 1 / 2 ^ 52 by decide +kernel]
    norm_num
  · refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
    rw [← PolyBound.ratOfWord_cast,
      show PolyBound.ratOfWord 0x3FEFFFFFFFFFFFFE = 1 - 1 / 2 ^ 52 by decide +kernel]
    norm_num

/-- The adjusted low part `l (1 ± 2^-52)` within `|l|/2^51 + 2^-1075` of `l`. -/
theorem adjust26 (l m : Float) (hl : Finite l.toBits) (hb : |value l.toBits| ≤ 2 ^ 1000) :
    Finite (l * (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) l *
        Lgamma.copySign (Float.ofBits 0x3E50000000000000) m)).toBits ∧
      |value (l * (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) l *
        Lgamma.copySign (Float.ofBits 0x3E50000000000000) m)).toBits - value l.toBits| ≤
        |value l.toBits| / 2 ^ 51 + 1 / 2 ^ 1075 := by
  obtain ⟨hFf, hFv⟩ := factor26 l m
  set F := 1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) l *
    Lgamma.copySign (Float.ofBits 0x3E50000000000000) m
  have hF1 : |value F.toBits| ≤ 1 + 1 / 2 ^ 52 := by
    have := abs_sub_abs_le_abs_sub (value F.toBits) 1
    rw [abs_one] at this
    linarith
  have hm := fapprox_mul (fapprox_self l hl) (fapprox_self F hFf) |value l.toBits|
    (1 + 1 / 2 ^ 52) le_rfl hF1 (|value l.toBits| * (1 + 1 / 2 ^ 52)) (by simp)
    (by nlinarith [(by norm_num : (2 : ℝ) ^ 1000 * (1 + 1 / 2 ^ 52) < 2 ^ 1022)])
  refine ⟨hm.1, ?_⟩
  have h2 := hm.2
  simp only [mul_zero, zero_mul, add_zero, zero_add] at h2
  have h3 : |value l.toBits * value F.toBits - value l.toBits| ≤ |value l.toBits| / 2 ^ 52 := by
    rw [show value l.toBits * value F.toBits - value l.toBits =
      value l.toBits * (value F.toBits - 1) by ring, abs_mul]
    have := mul_le_mul_of_nonneg_left hFv (abs_nonneg (value l.toBits))
    linarith
  have h4 := abs_sub_le (value (l * F).toBits) (value l.toBits * value F.toBits) (value l.toBits)
  have h5 : |value l.toBits| * (1 + 1 / 2 ^ 52) / 2 ^ 53 + |value l.toBits| / 2 ^ 52 ≤
      |value l.toBits| / 2 ^ 51 := by
    have := abs_nonneg (value l.toBits)
    nlinarith
  linarith

set_option maxHeartbeats 8000000 in
/-- **The renormalization** of a triple `a + b + c` with `|b| ≤ B` and `|c| ≤ C` into the pair
that the code passes on, in either branch of the adjustment. -/
theorem norm_spec (a b c : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hc : Finite c.toBits) (B C : ℝ) (hab : |value a.toBits| ≤ 2 ^ 850)
    (hbB : |value b.toBits| ≤ B) (hB : B ≤ 2 ^ 840) (hcC : |value c.toBits| ≤ C) (hC : C ≤ 2 ^ 800)
    (h1 l1 : Float) (e1 : fastTwoSum a b = (h1, l1))
    (l2 ll2 : Float) (e2 : fastTwoSum l1 c = (l2, ll2))
    (h3 l3 : Float) (e3 : fastTwoSum h1 l2 = (h3, l3))
    (l4 ll4 : Float) (e4 : fastTwoSum l3 ll2 = (l4, ll4))
    (cond : Bool) :
    let r : Float × Float := if cond = true then
        (h3, l4 * (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) l4 *
          Lgamma.copySign (Float.ofBits 0x3E50000000000000) ll4))
      else (h3, l4)
    Finite r.1.toBits ∧ Finite r.2.toBits ∧
      |value r.1.toBits + value r.2.toBits -
          (value a.toBits + value b.toBits + value c.toBits)| ≤
        (B + C) / 2 ^ 52 + (|value a.toBits| + B + C) / 2 ^ 99 + 1 / 2 ^ 1070 ∧
      |value r.2.toBits| ≤ (|value a.toBits| + B + C) / 2 ^ 48 + 1 / 2 ^ 1070 ∧
      |value r.1.toBits| ≤ (|value a.toBits| + B + C) * (1 + 1 / 2 ^ 50) := by
  intro r
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hbB
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) hcC
  set A := |value a.toBits| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  -- the first `fastTwoSum`
  obtain ⟨f1, g1, d1, k1, m1⟩ := TgammaAcc2.fts_approx a b ha hb A B le_rfl hbB
    (by linarith [(by norm_num : (2 : ℝ) ^ 850 + 2 ^ 840 ≤ 2 ^ 1000)])
  rw [e1] at f1 g1 d1 k1 m1
  dsimp only at f1 g1 d1 k1 m1
  -- the second
  obtain ⟨f2, g2, d2, k2, m2⟩ := TgammaAcc2.fts_approx l1 c g1 hc ((A + B) / 2 ^ 51) C m1 hcC
    (by linarith [(by norm_num : ((2 : ℝ) ^ 850 + 2 ^ 840) / 2 ^ 51 + 2 ^ 800 ≤ 2 ^ 1000)])
  rw [e2] at f2 g2 d2 k2 m2
  dsimp only at f2 g2 d2 k2 m2
  -- the third
  obtain ⟨f3, g3, d3, k3, m3⟩ := TgammaAcc2.fts_approx h1 l2 f1 f2 ((A + B) * (1 + 1 / 2 ^ 53))
    (((A + B) / 2 ^ 51 + C) * (1 + 1 / 2 ^ 53)) k1 k2
    (by nlinarith [(by norm_num : ((2 : ℝ) ^ 850 + 2 ^ 840) * (1 + 1 / 2 ^ 53) +
      (((2 : ℝ) ^ 850 + 2 ^ 840) / 2 ^ 51 + 2 ^ 800) * (1 + 1 / 2 ^ 53) ≤ 2 ^ 1000)])
  rw [e3] at f3 g3 d3 k3 m3
  dsimp only at f3 g3 d3 k3 m3
  -- the fourth
  have hS3 : (A + B) * (1 + 1 / 2 ^ 53) + ((A + B) / 2 ^ 51 + C) * (1 + 1 / 2 ^ 53) ≤
      (A + B + C) * (1 + 1 / 2 ^ 50) := by linarith
  have m3' : |value l3.toBits| ≤ (A + B + C) * (1 + 1 / 2 ^ 50) / 2 ^ 51 :=
    m3.trans (div_le_div_of_nonneg_right hS3 (by norm_num))
  have m2' : |value ll2.toBits| ≤ ((A + B) / 2 ^ 51 + C) / 2 ^ 51 := m2
  obtain ⟨f4, g4, d4, k4, m4⟩ := TgammaAcc2.fts_approx l3 ll2 g3 g2
    ((A + B + C) * (1 + 1 / 2 ^ 50) / 2 ^ 51) (((A + B) / 2 ^ 51 + C) / 2 ^ 51) m3' m2'
    (by nlinarith [(by norm_num : ((2 : ℝ) ^ 850 + 2 ^ 840 + 2 ^ 800) * (1 + 1 / 2 ^ 50) / 2 ^ 51 +
      (((2 : ℝ) ^ 850 + 2 ^ 840) / 2 ^ 51 + 2 ^ 800) / 2 ^ 51 ≤ 2 ^ 1000)])
  rw [e4] at f4 g4 d4 k4 m4
  dsimp only at f4 g4 d4 k4 m4
  -- the low part before the adjustment
  have hl4 : |value l4.toBits| ≤ (A + B + C) / 2 ^ 49 := by linarith
  -- the pair before the adjustment
  have hpair : |value h3.toBits + value l4.toBits - (value a.toBits + value b.toBits + value c.toBits)|
      ≤ (B + C) / 2 ^ 52 + (A + B + C) / 2 ^ 100 + 1 / 2 ^ 1071 := by
    have k : value h3.toBits + value l4.toBits - (value a.toBits + value b.toBits + value c.toBits) =
        (value h1.toBits + value l1.toBits - (value a.toBits + value b.toBits)) +
        (value l2.toBits + value ll2.toBits - (value l1.toBits + value c.toBits)) +
        (value h3.toBits + value l3.toBits - (value h1.toBits + value l2.toBits)) +
        (value l4.toBits + value ll4.toBits - (value l3.toBits + value ll2.toBits)) -
        value ll4.toBits := by ring
    rw [k]
    have e5 := abs_sub ((value h1.toBits + value l1.toBits - (value a.toBits + value b.toBits)) +
        (value l2.toBits + value ll2.toBits - (value l1.toBits + value c.toBits)) +
        (value h3.toBits + value l3.toBits - (value h1.toBits + value l2.toBits)) +
        (value l4.toBits + value ll4.toBits - (value l3.toBits + value ll2.toBits)))
      (value ll4.toBits)
    have e6 := abs_add_le ((value h1.toBits + value l1.toBits - (value a.toBits + value b.toBits)) +
        (value l2.toBits + value ll2.toBits - (value l1.toBits + value c.toBits)) +
        (value h3.toBits + value l3.toBits - (value h1.toBits + value l2.toBits)))
      (value l4.toBits + value ll4.toBits - (value l3.toBits + value ll2.toBits))
    have e7 := abs_add_le ((value h1.toBits + value l1.toBits - (value a.toBits + value b.toBits)) +
        (value l2.toBits + value ll2.toBits - (value l1.toBits + value c.toBits)))
      (value h3.toBits + value l3.toBits - (value h1.toBits + value l2.toBits))
    have e8 := abs_add_le (value h1.toBits + value l1.toBits - (value a.toBits + value b.toBits))
      (value l2.toBits + value ll2.toBits - (value l1.toBits + value c.toBits))
    linarith
  have hl4b : |value l4.toBits| ≤ 2 ^ 1000 := by
    linarith [(by norm_num : ((2 : ℝ) ^ 850 + 2 ^ 840 + 2 ^ 800) / 2 ^ 49 ≤ 2 ^ 1000)]
  obtain ⟨af, ad⟩ := adjust26 l4 ll4 f4 hl4b
  have hh3 : |value h3.toBits| ≤ (A + B + C) * (1 + 1 / 2 ^ 50) := by linarith
  show Finite r.1.toBits ∧ _
  by_cases hcnd : cond = true
  · have hr : r = (h3, l4 * (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) l4 *
        Lgamma.copySign (Float.ofBits 0x3E50000000000000) ll4)) := ite_eq_left hcnd
    rw [hr]
    dsimp only
    refine ⟨f3, af, ?_, ?_, hh3⟩
    · set L' := value (l4 * (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) l4 *
          Lgamma.copySign (Float.ofBits 0x3E50000000000000) ll4)).toBits
      have k : value h3.toBits + L' - (value a.toBits + value b.toBits + value c.toBits) =
          (value h3.toBits + value l4.toBits - (value a.toBits + value b.toBits + value c.toBits)) +
          (L' - value l4.toBits) := by ring
      rw [k]
      have := abs_add_le (value h3.toBits + value l4.toBits -
        (value a.toBits + value b.toBits + value c.toBits)) (L' - value l4.toBits)
      have h5 := div_le_div_of_nonneg_right hl4 (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
      linarith
    · have := abs_sub_abs_le_abs_sub (value (l4 * (1.0 + Lgamma.copySign
        (Float.ofBits 0x3E50000000000000) l4 *
          Lgamma.copySign (Float.ofBits 0x3E50000000000000) ll4)).toBits) (value l4.toBits)
      have h5 := div_le_div_of_nonneg_right hl4 (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
      linarith
  · have hr : r = (h3, l4) := ite_eq_right hcnd
    rw [hr]
    dsimp only
    refine ⟨f3, f4, ?_, ?_, hh3⟩
    · linarith
    · linarith

#print axioms factor26
#print axioms adjust26
#print axioms norm_spec

end Verified.Examples.LgammaAccNorm
