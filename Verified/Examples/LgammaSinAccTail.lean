import Verified.Examples.TgammaSinpidLow
import Verified.Examples.TgammaMul

/-!
The double-double steps of `Lgamma.asSinpipidAccurate` after its kernels: `A = d P` (`mulDDD`),
`B = (sh + sl) A` and `C1 = (ch + cl) Q` (`mulDD`), `C2 = C1 + B` (`fastSum`), `C3 = d C2`
(`mulDDD`), and `R = (sh + sl) + C3` (`fastSum`), for the table rows `sh + sl` and `ch + cl` and the
kernels `P ≈ sinAccCos (d²)` and `Q ≈ sinAccSin (d²)`.  `combine_c2` and `combine_r` are
`TgammaSinpidComb`'s lemmas with the bounds of the accurate kernels, whose errors are near `2^-110`
in place of `2^-72`; the low part of `Q`, at most `2^-55`, makes the low part of `R` at most `2^-47`
of its high part in place of `2^-50`.  `tail_spec` composes them: `R` lies within
`|d|/2^101 + sh/2^101 + 2^-1059` of `(sh + sl) + d ((ch + cl) Q + d P (sh + sl))`.
-/

namespace Verified.Examples.LgammaSinAccTail
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaSinpidSum
  TgammaSinpidLow

set_option exponentiation.threshold 4096

/-- The code of `asSinpipidAccurate` after the kernels. -/
def sinAccTail (d sh sl ch cl P1 P2 Q1 Q2 : Float) : Float × Float :=
  let A := mulDDD d P1 P2
  let B := mulDD sh sl A.1 A.2
  let C1 := mulDD ch cl Q1 Q2
  let C2 := fastSum C1.1 C1.2 B.1 B.2
  let C3 := mulDDD d C2.1 C2.2
  fastSum sh sl C3.1 C3.2

/-- **`A = d P`.** -/
theorem stepA (hF : FmaSpec.FmaNearest) (d P1 P2 : Float) (hd : Finite d.toBits)
    (hp1 : Finite P1.toBits) (hp2 : Finite P2.toBits) (hD : |value d.toBits| ≤ 1 / 2)
    (hP1 : |value P1.toBits| ≤ 1 / 3299) (hP2 : |value P2.toBits| ≤ 1 / 2 ^ 61) :
    Finite (mulDDD d P1 P2).1.toBits ∧ Finite (mulDDD d P1 P2).2.toBits ∧
      |value (mulDDD d P1 P2).1.toBits + value (mulDDD d P1 P2).2.toBits -
          value d.toBits * (value P1.toBits + value P2.toBits)| ≤ |value d.toBits| / 2 ^ 112 + 1 / 2 ^ 1072 ∧
      |value (mulDDD d P1 P2).1.toBits| ≤ |value d.toBits| / 3298 + 1 / 2 ^ 1075 ∧
      |value (mulDDD d P1 P2).2.toBits| ≤ |value d.toBits| / 2 ^ 60 + 1 / 2 ^ 1071 := by
  have hD0 := abs_nonneg (value d.toBits)
  have hHm : 1 / 3299 * |value d.toBits| ≤ 2 ^ 900 := by
    have := mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 1 / 3299)
    linarith [(by norm_num : (1 : ℝ) / 3299 * (1 / 2) ≤ 2 ^ 900)]
  have hLm : 1 / 2 ^ 61 * |value d.toBits| ≤ 2 ^ 900 := by
    have := mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 61)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 61 * (1 / 2) ≤ 2 ^ 900)]
  obtain ⟨h1, h2, he, hl, hh⟩ := mulDDD_spec hF d P1 P2 hd hp1 hp2 (1 / 3299 * |value d.toBits|)
    (1 / 2 ^ 61 * |value d.toBits|) (mul_le_mul_of_nonneg_right hP1 hD0)
    (mul_le_mul_of_nonneg_right hP2 hD0) hHm hLm
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · have k := mul_le_mul_of_nonneg_right (show (3 * (1 / 2 ^ 61) + 1 / 3299 / 2 ^ 51 : ℝ) / 2 ^ 53 ≤
      1 / 2 ^ 112 by norm_num) hD0
    linarith
  · have k := mul_le_mul_of_nonneg_right (show (1 / 3299 : ℝ) * (1 + 1 / 2 ^ 53) ≤ 1 / 3298 by
      norm_num) hD0
    linarith
  · have k := mul_le_mul_of_nonneg_right (show (1 / 2 ^ 61 : ℝ) * (1 + 1 / 2 ^ 51) +
      1 / 3299 / 2 ^ 52 ≤ 1 / 2 ^ 60 by norm_num) hD0
    linarith

/-- **`B = (sh + sl) A`**, in terms of `Sh = sh`. -/
theorem stepB (hF : FmaSpec.FmaNearest) (sh sl A1 A2 : Float) (hsh : Finite sh.toBits)
    (hsl : Finite sl.toBits) (ha1 : Finite A1.toBits) (ha2 : Finite A2.toBits) (Sh : ℝ)
    (hShv : value sh.toBits = Sh) (hSh0 : 0 ≤ Sh) (hSh1 : Sh ≤ 1)
    (hslb : |value sl.toBits| ≤ Sh / 2 ^ 53)
    (hA1 : |value A1.toBits| ≤ 1 / 6596 + 1 / 2 ^ 1075)
    (hA2 : |value A2.toBits| ≤ 1 / 2 ^ 61 + 1 / 2 ^ 1071) :
    Finite (mulDD sh sl A1 A2).1.toBits ∧ Finite (mulDD sh sl A1 A2).2.toBits ∧
      |value (mulDD sh sl A1 A2).1.toBits + value (mulDD sh sl A1 A2).2.toBits -
          (value sh.toBits + value sl.toBits) * (value A1.toBits + value A2.toBits)| ≤
        Sh / 2 ^ 111 + 1 / 2 ^ 1067 ∧
      |value (mulDD sh sl A1 A2).1.toBits| ≤ Sh / 6594 + 1 / 2 ^ 1073 ∧
      |value (mulDD sh sl A1 A2).2.toBits| ≤ Sh / 2 ^ 60 + 1 / 2 ^ 1068 := by
  have habs : |value sh.toBits| = Sh := by rw [hShv, abs_of_nonneg hSh0]
  have hsl0 := abs_nonneg (value sl.toBits)
  obtain ⟨h1, h2, he, hl, hh⟩ := mulDD_spec hF sh sl A1 A2 hsh hsl ha1 ha2
    ((1 / 6596 + 1 / 2 ^ 1075) * Sh) ((1 / 6596 + 1 / 2 ^ 1075) * (Sh / 2 ^ 53))
    ((1 / 2 ^ 61 + 1 / 2 ^ 1071) * Sh) ((1 / 2 ^ 61 + 1 / 2 ^ 1071) * (Sh / 2 ^ 53))
    (by rw [habs]; exact mul_le_mul_of_nonneg_right hA1 hSh0)
    (mul_le_mul hA1 hslb hsl0 (by positivity))
    (by rw [habs]; exact mul_le_mul_of_nonneg_right hA2 hSh0)
    (mul_le_mul hA2 hslb hsl0 (by positivity))
    (by linarith [(by norm_num : (1 / 6596 + 1 / 2 ^ 1075 : ℝ) ≤ 2 ^ 900),
      mul_le_mul_of_nonneg_left hSh1 (by norm_num : (0 : ℝ) ≤ 1 / 6596 + 1 / 2 ^ 1075)])
    (by linarith [(by norm_num : (1 / 6596 + 1 / 2 ^ 1075 : ℝ) / 2 ^ 53 + (1 / 2 ^ 61 + 1 / 2 ^ 1071) ≤
      2 ^ 900)])
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · have k := mul_le_mul_of_nonneg_right (show (1 / 2 ^ 61 + 1 / 2 ^ 1071 : ℝ) / 2 ^ 53 +
      (4 * ((1 / 6596 + 1 / 2 ^ 1075) / 2 ^ 53 + (1 / 2 ^ 61 + 1 / 2 ^ 1071)) +
        (1 / 6596 + 1 / 2 ^ 1075) / 2 ^ 51) / 2 ^ 53 ≤ 1 / 2 ^ 111 by norm_num) hSh0
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1070 ≤ 1 / 2 ^ 1067)]
  · have k := mul_le_mul_of_nonneg_right (show (1 / 6596 + 1 / 2 ^ 1075 : ℝ) * (1 + 1 / 2 ^ 53) ≤
      1 / 6594 + 1 / 2 ^ 1074 by norm_num) hSh0
    have k2 := mul_le_mul_of_nonneg_left hSh1 (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 1074)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 1073)]
  · have k := mul_le_mul_of_nonneg_right (show ((1 / 6596 + 1 / 2 ^ 1075 : ℝ) / 2 ^ 53 +
      (1 / 2 ^ 61 + 1 / 2 ^ 1071)) * (1 + 1 / 2 ^ 50) + (1 / 6596 + 1 / 2 ^ 1075) / 2 ^ 52 ≤
        1 / 2 ^ 60 by norm_num) hSh0
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1070 ≤ 1 / 2 ^ 1068)]

/-- **`C1 = (ch + cl) Q`**, in terms of `Ch = ch`, with the lower bound of its high part. -/
theorem stepC (hF : FmaSpec.FmaNearest) (ch cl Q1 Q2 : Float) (hch : Finite ch.toBits)
    (hcl : Finite cl.toBits) (hq1 : Finite Q1.toBits) (hq2 : Finite Q2.toBits) (Ch : ℝ)
    (hChv : value ch.toBits = Ch) (hCh0 : 0 ≤ Ch) (hCh1 : Ch ≤ 1)
    (hclb : |value cl.toBits| ≤ Ch / 2 ^ 53)
    (hQ1 : 245 / 10 ^ 4 ≤ value Q1.toBits ∧ value Q1.toBits ≤ 2456 / 10 ^ 5)
    (hQ2 : |value Q2.toBits| ≤ 1 / 2 ^ 55) :
    Finite (mulDD ch cl Q1 Q2).1.toBits ∧ Finite (mulDD ch cl Q1 Q2).2.toBits ∧
      |value (mulDD ch cl Q1 Q2).1.toBits + value (mulDD ch cl Q1 Q2).2.toBits -
          (value ch.toBits + value cl.toBits) * (value Q1.toBits + value Q2.toBits)| ≤
        Ch / 2 ^ 105 + 1 / 2 ^ 1069 ∧
      |value (mulDD ch cl Q1 Q2).1.toBits| ≤ Ch * (2457 / 10 ^ 5) + 1 / 2 ^ 1075 ∧
      |value (mulDD ch cl Q1 Q2).2.toBits| ≤ Ch / 2 ^ 54 + 1 / 2 ^ 1069 ∧
      Ch * (2449 / 10 ^ 5) - 1 / 2 ^ 1068 ≤ |value (mulDD ch cl Q1 Q2).1.toBits| := by
  have habs : |value ch.toBits| = Ch := by rw [hChv, abs_of_nonneg hCh0]
  have hq1abs : |value Q1.toBits| ≤ 2456 / 10 ^ 5 := by
    rw [abs_of_nonneg (by linarith)]; exact hQ1.2
  have hcl0 := abs_nonneg (value cl.toBits)
  obtain ⟨h1, h2, he, hl, hh⟩ := mulDD_spec hF ch cl Q1 Q2 hch hcl hq1 hq2
    (2456 / 10 ^ 5 * Ch) (2456 / 10 ^ 5 * (Ch / 2 ^ 53)) (1 / 2 ^ 55 * Ch) (1 / 2 ^ 55 * (Ch / 2 ^ 53))
    (by rw [habs]; exact mul_le_mul_of_nonneg_right hq1abs hCh0)
    (mul_le_mul hq1abs hclb hcl0 (by norm_num))
    (by rw [habs]; exact mul_le_mul_of_nonneg_right hQ2 hCh0)
    (mul_le_mul hQ2 hclb hcl0 (by norm_num))
    (by linarith) (by linarith)
  -- the lower bound of the high part, which is `Q1 ch` rounded
  have hlo : Ch * (2449 / 10 ^ 5) - 1 / 2 ^ 1068 ≤ |value (mulDD ch cl Q1 Q2).1.toBits| := by
    have he1 : (mulDD ch cl Q1 Q2).1 = Q1 * ch := rfl
    have ha := fapprox_mul (fapprox_self Q1 hq1) (fapprox_self ch hch) (2456 / 10 ^ 5) Ch hq1abs
      (le_of_eq habs) (2456 / 10 ^ 5 * Ch) (by simp) (by linarith)
    rw [← he1] at ha
    have ha2 := ha.2
    have hprod : 245 / 10 ^ 4 * Ch ≤ |value Q1.toBits * value ch.toBits| := by
      rw [abs_mul, habs, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_right hQ1.1 hCh0
    have := abs_sub_abs_le_abs_sub (value Q1.toBits * value ch.toBits)
      (value (mulDD ch cl Q1 Q2).1.toBits)
    rw [abs_sub_comm] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1068)]
  refine ⟨h1, h2, ?_, ?_, ?_, hlo⟩
  · have k := mul_le_mul_of_nonneg_right (show (1 / 2 ^ 55 : ℝ) / 2 ^ 53 +
      (4 * (2456 / 10 ^ 5 / 2 ^ 53 + 1 / 2 ^ 55) + 2456 / 10 ^ 5 / 2 ^ 51) / 2 ^ 53 ≤ 1 / 2 ^ 105 by
        norm_num) hCh0
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1070 ≤ 1 / 2 ^ 1069)]
  · have k := mul_le_mul_of_nonneg_right (show (2456 / 10 ^ 5 : ℝ) * (1 + 1 / 2 ^ 53) ≤ 2457 / 10 ^ 5 by
      norm_num) hCh0
    linarith
  · have k := mul_le_mul_of_nonneg_right (show (2456 / 10 ^ 5 / 2 ^ 53 + 1 / 2 ^ 55 : ℝ) *
      (1 + 1 / 2 ^ 50) + 2456 / 10 ^ 5 / 2 ^ 52 ≤ 1 / 2 ^ 54 by norm_num) hCh0
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1070 ≤ 1 / 2 ^ 1069)]

/-- **The sum `C2 = C1 + P`** of the accurate sine, from bounds on `C1` in terms of `Ch` and on `P` in
terms of `Sh`. -/
theorem combine_c2 (C1 P : Float × Float) (h11 : Finite C1.1.toBits) (h12 : Finite C1.2.toBits)
    (hp1 : Finite P.1.toBits) (hp2 : Finite P.2.toBits) (Ch Sh A1 A2 : ℝ)
    (hCh0 : 0 ≤ Ch) (hCh1 : Ch ≤ 1) (hSh0 : 0 ≤ Sh) (hSh1 : Sh ≤ 1)
    (hC1 : |value C1.1.toBits + value C1.2.toBits - A1| ≤ Ch / 2 ^ 105 + 1 / 2 ^ 1069)
    (hC1a : |value C1.1.toBits| ≤ Ch * (2457 / 10 ^ 5) + 1 / 2 ^ 1075)
    (hC1b : |value C1.2.toBits| ≤ Ch / 2 ^ 54 + 1 / 2 ^ 1069)
    (hC1lo : Ch * (2449 / 10 ^ 5) - 1 / 2 ^ 1068 ≤ |value C1.1.toBits|)
    (hP : |value P.1.toBits + value P.2.toBits - A2| ≤ Sh / 2 ^ 111 + 1 / 2 ^ 1067)
    (hPa : |value P.1.toBits| ≤ Sh / 6594 + 1 / 2 ^ 1073)
    (hPb : |value P.2.toBits| ≤ Sh / 2 ^ 60 + 1 / 2 ^ 1068)
    (hA : Ch = 0 ∨ (1 / 2 ^ 60 ≤ Ch ∧ Sh ≤ 100 * Ch)) :
    let C2 := fastSum C1.1 C1.2 P.1 P.2
    Finite C2.1.toBits ∧ Finite C2.2.toBits ∧
      |value C2.1.toBits + value C2.2.toBits - (A1 + A2)| ≤
        Ch / 2 ^ 104 + Sh / 2 ^ 110 + 1 / 2 ^ 1060 ∧
      |value C2.1.toBits| ≤ Ch * (2458 / 10 ^ 5) + Sh / 6593 + 1 / 2 ^ 1060 ∧
      |value C2.2.toBits| ≤ Ch / 2 ^ 53 + Sh / 2 ^ 59 + 1 / 2 ^ 1060 ∧
      Ch * (2448 / 10 ^ 5) - Sh / 6593 - 1 / 2 ^ 1060 ≤ |value C2.1.toBits| := by
  intro C2
  have hcond : |value P.1.toBits| ≤ |value C1.1.toBits| ∨ value C1.1.toBits = 0 := by
    rcases hA with h0 | ⟨h1, h2⟩
    · right
      apply value_zero_of_small
      rw [h0] at hC1a
      linarith [(by norm_num : (0 : ℝ) * (2457 / 10 ^ 5) + 1 / 2 ^ 1075 < 1 / 2 ^ 1074)]
    · left
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1073 + 1 / 2 ^ 1068 ≤
        (2449 / 10 ^ 5 - 100 / 6594) * (1 / 2 ^ 60))]
  have hx : |value C1.1.toBits| < 2 ^ 898 := by
    linarith [(by norm_num : (1 : ℝ) * (2457 / 10 ^ 5) + 1 / 2 ^ 1075 < 2 ^ 898)]
  have hy : |value P.1.toBits| < 2 ^ 898 := by
    linarith [(by norm_num : (1 : ℝ) / 6594 + 1 / 2 ^ 1073 < 2 ^ 898)]
  obtain ⟨hf1, hf2, he, hl⟩ := fastSum_spec' C1.1 C1.2 P.1 P.2 h11 h12 hp1 hp2 hcond hx hy
    (Ch / 2 ^ 54 + Sh / 2 ^ 60 + 1 / 2 ^ 1067)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1069 + 1 / 2 ^ 1068 ≤ 1 / 2 ^ 1067)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 54 + 1 / 2 ^ 60 + 1 / 2 ^ 1067 ≤ 2 ^ 800)])
  have hlow := fastSum_low C1.1 C1.2 P.1 P.2 h11 h12 hp1 hp2 hcond hx hy
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 54 + 1 / 2 ^ 1069 ≤ 2 ^ 800)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 + 1 / 2 ^ 1068 ≤ 2 ^ 800)])
  refine ⟨hf1, hf2, ?_⟩
  obtain ⟨a, ha⟩ : ∃ a, a = value C2.1.toBits := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = value C2.2.toBits := ⟨_, rfl⟩
  obtain ⟨x1, hx1⟩ : ∃ v, v = value C1.1.toBits := ⟨_, rfl⟩
  obtain ⟨x2, hx2⟩ : ∃ v, v = value C1.2.toBits := ⟨_, rfl⟩
  obtain ⟨p1, hp1'⟩ : ∃ v, v = value P.1.toBits := ⟨_, rfl⟩
  obtain ⟨p2, hp2'⟩ : ∃ v, v = value P.2.toBits := ⟨_, rfl⟩
  rw [← ha, ← hb] at he hl hlow ⊢
  rw [← hx1, ← hx2, ← hp1', ← hp2'] at he
  rw [← hx2, ← hp2'] at hlow
  rw [← hx1, ← hx2] at hC1
  rw [← hx1] at hC1a hC1lo
  rw [← hx2] at hC1b
  rw [← hp1', ← hp2'] at hP
  rw [← hp1'] at hPa
  rw [← hp2'] at hPb
  have t1 : |a| ≤ |a + b| + |b| := by
    have := abs_add_le (a + b) (-b); rw [abs_neg, add_neg_cancel_right] at this; exact this
  have t2 : |a + b| ≤ |x1 + x2 + (p1 + p2)| + |a + b - (x1 + x2 + (p1 + p2))| := by
    have := abs_add_le (x1 + x2 + (p1 + p2)) (a + b - (x1 + x2 + (p1 + p2)))
    rw [add_sub_cancel] at this; exact this
  have t3 : |x1 + x2 + (p1 + p2)| ≤ |x1| + |x2| + (|p1| + |p2|) := by
    have h1 := abs_add_le (x1 + x2) (p1 + p2)
    have h2 := abs_add_le x1 x2
    have h3 := abs_add_le p1 p2
    linarith
  have hab : |a| ≤ Ch * (2458 / 10 ^ 5) + Sh / 6593 + 1 / 2 ^ 1060 := by
    linarith
  have t4 : |a + b - (A1 + A2)| ≤ |a + b - (x1 + x2 + (p1 + p2))| + |x1 + x2 - A1| +
      |p1 + p2 - A2| := by
    have h1 := abs_add_le (a + b - (x1 + x2 + (p1 + p2))) (x1 + x2 - A1)
    have h2 := abs_add_le (a + b - (x1 + x2 + (p1 + p2)) + (x1 + x2 - A1)) (p1 + p2 - A2)
    rw [show a + b - (x1 + x2 + (p1 + p2)) + (x1 + x2 - A1) + (p1 + p2 - A2) =
      a + b - (A1 + A2) by ring] at h2
    linarith
  have hbt : |b| ≤ Ch / 2 ^ 53 + Sh / 2 ^ 59 + 1 / 2 ^ 1060 := by
    linarith
  refine ⟨?_, hab, hbt, ?_⟩
  · linarith
  · have t5 : |x1| ≤ |x1 + x2 + (p1 + p2)| + |x2| + |p1| + |p2| := by
      have h1 := abs_add_le (x1 + x2 + (p1 + p2)) (-(x2 + (p1 + p2)))
      rw [abs_neg, show x1 + x2 + (p1 + p2) + -(x2 + (p1 + p2)) = x1 by ring] at h1
      have h2 := abs_add_le x2 (p1 + p2)
      have h3 := abs_add_le p1 p2
      linarith
    have t6 : |x1 + x2 + (p1 + p2)| ≤ |a + b| + |a + b - (x1 + x2 + (p1 + p2))| := by
      have h1 := abs_add_le (a + b) (-(a + b - (x1 + x2 + (p1 + p2))))
      rw [abs_neg, show a + b + -(a + b - (x1 + x2 + (p1 + p2))) = x1 + x2 + (p1 + p2) by ring]
        at h1
      exact h1
    have t7 := abs_add_le a b
    linarith

set_option maxHeartbeats 1000000 in
/-- **The product `C3 = d C2` and the result `R = (sh + sl) + C3`** of the accurate sine. -/
theorem combine_r (hF : FmaSpec.FmaNearest) (d sh sl : Float) (C2 : Float × Float)
    (hd : Finite d.toBits) (hsh : Finite sh.toBits) (hsl : Finite sl.toBits)
    (h21 : Finite C2.1.toBits) (h22 : Finite C2.2.toBits) (Ch A : ℝ)
    (hD : |value d.toBits| ≤ 1 / 2) (hCh0 : 0 ≤ Ch) (hCh1 : Ch ≤ 1)
    (hSh0 : 0 ≤ value sh.toBits) (hSh1 : value sh.toBits ≤ 1)
    (hslb : |value sl.toBits| ≤ value sh.toBits / 2 ^ 53)
    (hC2 : |value C2.1.toBits + value C2.2.toBits - A| ≤
      Ch / 2 ^ 104 + value sh.toBits / 2 ^ 110 + 1 / 2 ^ 1060)
    (hC2a : |value C2.1.toBits| ≤ Ch * (2458 / 10 ^ 5) + value sh.toBits / 6593 + 1 / 2 ^ 1060)
    (hC2bt : |value C2.2.toBits| ≤
      Ch / 2 ^ 53 + value sh.toBits / 2 ^ 59 + 1 / 2 ^ 1060)
    (hC2lo : Ch * (2448 / 10 ^ 5) - value sh.toBits / 6593 - 1 / 2 ^ 1060 ≤ |value C2.1.toBits|)
    (hB : value sh.toBits = 0 ∨ (1 / 2 ^ 60 ≤ value sh.toBits ∧
      2 ^ 53 * |value sl.toBits| + Ch * (1535 / 10 ^ 4) ≤ value sh.toBits * (69 / 10)))
    (hZ : value sh.toBits = 0 → 1 / 2 ^ 60 ≤ Ch ∧ 1 / 2 ^ 47 ≤ |value d.toBits|) :
    let C3 := mulDDD d C2.1 C2.2
    let R := fastSum sh sl C3.1 C3.2
    Finite R.1.toBits ∧ Finite R.2.toBits ∧
      |value R.1.toBits + value R.2.toBits -
          (value sh.toBits + value sl.toBits + value d.toBits * A)| ≤
        |value d.toBits| / 2 ^ 102 + value sh.toBits / 2 ^ 102 + 1 / 2 ^ 1060 ∧
      |value R.2.toBits| ≤ |value R.1.toBits| / 2 ^ 47 := by
  intro C3 R
  obtain ⟨D, hDd⟩ : ∃ v, v = value d.toBits := ⟨_, rfl⟩
  obtain ⟨Sh, hShd⟩ : ∃ v, v = value sh.toBits := ⟨_, rfl⟩
  rw [← hDd] at hD hZ ⊢
  rw [← hShd] at hSh0 hSh1 hslb hC2 hC2a hC2bt hC2lo hB hZ ⊢
  have hC2b : |value C2.2.toBits| ≤ Ch / 2 ^ 53 + Sh / 2 ^ 59 + 1 / 2 ^ 1060 := by
    linarith
  have hD0 : 0 ≤ |D| := abs_nonneg D
  obtain ⟨M2, hM2⟩ : ∃ v, v = Ch * (2458 / 10 ^ 5) + Sh / 6593 + 1 / 2 ^ 1060 := ⟨_, rfl⟩
  obtain ⟨L2, hL2⟩ : ∃ v, v = Ch / 2 ^ 53 + Sh / 2 ^ 59 + 1 / 2 ^ 1060 := ⟨_, rfl⟩
  rw [← hM2] at hC2a
  rw [← hL2] at hC2b
  have hM20 : 0 ≤ M2 := by
    rw [hM2]; linarith [(by norm_num : (0 : ℝ) < 1 / 2 ^ 1060)]
  have hL20 : 0 ≤ L2 := by
    rw [hL2]; linarith [(by norm_num : (0 : ℝ) < 1 / 2 ^ 1060)]
  have hM2b : M2 ≤ 1 / 40 := by
    rw [hM2]; linarith [(by norm_num : (2458 / 10 ^ 5 : ℝ) + 1 / 6593 + 1 / 2 ^ 1060 ≤ 1 / 40)]
  have hL2b : L2 ≤ 1 / 2 ^ 53 + 1 / 2 ^ 59 + 1 / 2 ^ 1060 := by
    rw [hL2]; linarith
  obtain ⟨H, hH⟩ : ∃ v, v = M2 * |D| := ⟨_, rfl⟩
  obtain ⟨Lw, hLw⟩ : ∃ v, v = L2 * |D| := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := by rw [hH]; exact mul_nonneg hM20 hD0
  have hLw0 : 0 ≤ Lw := by rw [hLw]; exact mul_nonneg hL20 hD0
  have hHM : H ≤ M2 / 2 := by
    rw [hH]; have := mul_le_mul_of_nonneg_left hD hM20; linarith
  have hHD : H ≤ |D| / 40 := by
    rw [hH]; have := mul_le_mul_of_nonneg_right hM2b hD0; linarith
  have hLwD : Lw ≤ (1 / 2 ^ 53 + 1 / 2 ^ 59 + 1 / 2 ^ 1060) * |D| := by
    rw [hLw]; exact mul_le_mul_of_nonneg_right hL2b hD0
  have hDb : |D| ≤ 1 / 2 := hD
  obtain ⟨h31, h32, he3, hl3, hh3⟩ := mulDDD_spec hF d C2.1 C2.2 hd h21 h22 H Lw
    (by rw [hH, ← hDd]; exact mul_le_mul_of_nonneg_right hC2a (abs_nonneg _))
    (by rw [hLw, ← hDd]; exact mul_le_mul_of_nonneg_right hC2b (abs_nonneg _))
    (by linarith [(by norm_num : (1 : ℝ) / 2 / 40 ≤ 2 ^ 900)])
    (by linarith [(by norm_num : (1 / 2 ^ 53 + 1 / 2 ^ 59 + 1 / 2 ^ 1060 : ℝ) * (1 / 2) ≤ 2 ^ 900),
      mul_le_mul_of_nonneg_left hDb (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 53 + 1 / 2 ^ 59 + 1 / 2 ^ 1060)])
  rw [← hDd] at he3
  have hcond : |value C3.1.toBits| ≤ |value sh.toBits| ∨ value sh.toBits = 0 := by
    rw [← hShd]
    rcases hB with h0 | ⟨h1, h2⟩
    · right; exact h0
    · left
      rw [abs_of_nonneg hSh0]
      have h50 : Ch ≤ 50 * Sh := by
        have := abs_nonneg (value sl.toBits)
        linarith [(by norm_num : (0 : ℝ) ≤ 2 ^ 53)]
      have : M2 ≤ Sh * (50 * (2458 / 10 ^ 5) + 1 / 6593) + 1 / 2 ^ 1060 := by
        rw [hM2]; nlinarith
      linarith [(by norm_num : ((50 * (2458 / 10 ^ 5) + 1 / 6593 : ℝ) / 2) * (1 + 1 / 2 ^ 53) ≤
        7 / 10), (by norm_num : (1 / 2 ^ 1060 : ℝ) / 2 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
        3 / 10 * (1 / 2 ^ 60))]
  have hx : |value sh.toBits| < 2 ^ 898 := by
    rw [← hShd, abs_of_nonneg hSh0]; linarith [(by norm_num : (1 : ℝ) < 2 ^ 898)]
  have hy : |value C3.1.toBits| < 2 ^ 898 := by
    linarith [(by norm_num : (1 : ℝ) / 2 / 40 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 < 2 ^ 898)]
  obtain ⟨LR, hLR⟩ : ∃ v, v = Sh / 2 ^ 52 + (Lw * (1 + 1 / 2 ^ 51) + H / 2 ^ 52 + 1 / 2 ^ 1071) :=
    ⟨_, rfl⟩
  obtain ⟨hr1, hr2, her, hlr⟩ := fastSum_spec' sh sl C3.1 C3.2 hsh hsl h31 h32 hcond hx hy LR
    (by rw [hLR]; linarith)
    (by rw [hLR]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 +
      ((1 / 2 ^ 53 + 1 / 2 ^ 59 + 1 / 2 ^ 1060) * (1 / 2) * (1 + 1 / 2 ^ 51) +
        1 / 2 / 40 / 2 ^ 52 + 1 / 2 ^ 1071) ≤ 2 ^ 800)])
  have hRlow := fastSum_low sh sl C3.1 C3.2 hsh hsl h31 h32 hcond hx hy
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 53 ≤ 2 ^ 800)])
    (by linarith [(by norm_num : ((1 / 2 ^ 53 + 1 / 2 ^ 59 + 1 / 2 ^ 1060 : ℝ) * (1 / 2)) *
      (1 + 1 / 2 ^ 51) + 1 / 2 / 40 / 2 ^ 52 + 1 / 2 ^ 1071 ≤ 2 ^ 800)])
  have hC3low := mulDDD_low hF d C2.1 C2.2 hd h21 h22
    (by rw [← hDd]; have := mul_le_mul_of_nonneg_right hC2a hD0
        linarith [(by norm_num : (1 : ℝ) / 2 / 40 ≤ 2 ^ 900)])
    (by rw [← hDd]; have := mul_le_mul_of_nonneg_right hC2b hD0
        linarith [(by norm_num : (1 / 2 ^ 53 + 1 / 2 ^ 59 + 1 / 2 ^ 1060 : ℝ) * (1 / 2) ≤ 2 ^ 900)])
  rw [← hDd] at hC3low
  obtain ⟨-, -, hfe⟩ := fts_exact sh C3.1 hsh h31 hcond hx hy
  have hft := fts_low sh C3.1 hsh h31 (by
    have := abs_add_le (value sh.toBits) (value C3.1.toBits)
    linarith [(by norm_num : (2 : ℝ) ^ 898 + 2 ^ 898 < 2 ^ 1023)]) hfe
  have hs1 : (fastSum sh sl C3.1 C3.2).1 = (fastTwoSum sh C3.1).1 := by simp only [fastSum]
  rw [← hs1] at hfe hft
  obtain ⟨tt, htt⟩ : ∃ v, v = value (fastTwoSum sh C3.1).2.toBits := ⟨_, rfl⟩
  rw [← htt] at hfe hft
  rw [← hShd] at hfe
  refine ⟨hr1, hr2, ?_⟩
  rw [← hShd] at her
  obtain ⟨r1, hr1d⟩ : ∃ v, v = value R.1.toBits := ⟨_, rfl⟩
  obtain ⟨r2, hr2d⟩ : ∃ v, v = value R.2.toBits := ⟨_, rfl⟩
  obtain ⟨c1, hc1d⟩ : ∃ v, v = value C3.1.toBits := ⟨_, rfl⟩
  obtain ⟨c2, hc2d⟩ : ∃ v, v = value C3.2.toBits := ⟨_, rfl⟩
  obtain ⟨s2, hs2d⟩ : ∃ v, v = value C2.1.toBits + value C2.2.toBits := ⟨_, rfl⟩
  obtain ⟨vl, hvl⟩ : ∃ v, v = value sl.toBits := ⟨_, rfl⟩
  rw [← hr1d, ← hr2d] at her hlr hRlow ⊢
  rw [← hr1d] at hfe hft
  rw [← hc1d] at hfe
  rw [← hc1d, ← hc2d] at hC3low
  rw [← hc2d, ← hvl] at hRlow
  rw [← hc1d, ← hc2d, ← hvl] at her
  rw [← hvl]
  rw [← hc1d, ← hc2d, ← hs2d] at he3
  rw [← hc1d] at hh3
  rw [← hc2d] at hl3
  rw [← hs2d] at hC2
  rw [← hvl] at hslb hB
  -- the magnitude of `r1`
  have t1 : |r1| ≤ |r1 + r2| + |r2| := by
    have := abs_add_le (r1 + r2) (-r2); rw [abs_neg, add_neg_cancel_right] at this; exact this
  have t2 : |r1 + r2| ≤ |Sh + vl + (c1 + c2)| + |r1 + r2 - (Sh + vl + (c1 + c2))| := by
    have := abs_add_le (Sh + vl + (c1 + c2)) (r1 + r2 - (Sh + vl + (c1 + c2)))
    rw [add_sub_cancel] at this; exact this
  have t3 : |Sh + vl + (c1 + c2)| ≤ Sh + |vl| + (|c1| + |c2|) := by
    have h1 := abs_add_le (Sh + vl) (c1 + c2)
    have h2 := abs_add_le Sh vl
    have h3 := abs_add_le c1 c2
    rw [abs_of_nonneg hSh0] at h2
    linarith
  have hr1b : |r1| ≤ 2 * Sh + |D| + 1 / 2 ^ 1060 := by
    rw [hLR] at her hlr
    linarith
  -- the error
  have hE2 : |D| * |s2 - A| ≤ |D| * (1 / 2 ^ 104 + 1 / 2 ^ 110 + 1 / 2 ^ 1060) := by
    apply mul_le_mul_of_nonneg_left _ hD0
    linarith
  have t4 : |r1 + r2 - (Sh + vl + D * A)| ≤ |r1 + r2 - (Sh + vl + (c1 + c2))| +
      |c1 + c2 - D * s2| + |D| * |s2 - A| := by
    have h1 := abs_add_le (r1 + r2 - (Sh + vl + (c1 + c2))) (c1 + c2 - D * s2)
    have h2 := abs_add_le (r1 + r2 - (Sh + vl + (c1 + c2)) + (c1 + c2 - D * s2)) (D * (s2 - A))
    rw [show r1 + r2 - (Sh + vl + (c1 + c2)) + (c1 + c2 - D * s2) + D * (s2 - A) =
      r1 + r2 - (Sh + vl + D * A) by ring, abs_mul] at h2
    linarith
  rw [hLR] at her hlr
  constructor
  · linarith
  · have hr1lo : Sh ≤ |r1| + |tt| + |c1| := by
      have := le_abs_self r1; have := le_abs_self tt; have := neg_abs_le c1
      linarith
    obtain ⟨hC3a, hC3b⟩ := hC3low
    rcases hB with h0 | ⟨h1, h2⟩
    · obtain ⟨hCh60, hD46⟩ := hZ h0
      subst h0
      have hc1r : |c1| ≤ |r1| + |tt| := by
        rw [show c1 = r1 + tt by linarith]; exact abs_add_le r1 tt
      have hvl0 : |vl| = 0 := by
        have := abs_nonneg vl; linarith
      have hDS := mul_le_mul_of_nonneg_right hC2bt hD0
      have hlo2 := mul_le_mul_of_nonneg_right hC2lo hD0
      have hW : 1 / 2 ^ 60 * (1 / 2 ^ 47) ≤ Ch * |D| :=
        mul_le_mul hCh60 hD46 (by norm_num) hCh0
      linarith
    · have hDS := mul_le_mul_of_nonneg_right hC2bt hD0
      have hDS2 := mul_le_mul_of_nonneg_left hDb
        (by linarith : (0 : ℝ) ≤ Ch / 2 ^ 53 + Sh / 2 ^ 59 + 1 / 2 ^ 1060)
      have hvl0 := abs_nonneg vl
      have hr10 := abs_nonneg r1
      -- `ch ≤ 44.96 sh` from the condition on the row, then the parts of `C3`
      have hCh : Ch ≤ 4496 / 100 * Sh := by linarith only [h2, hvl0, hSh0]
      have hc1b : |c1| ≤ Ch * (12291 / 10 ^ 6) + Sh / 13000 + 1 / 2 ^ 1059 := by
        rw [hM2] at hHM
        linarith only [hh3, hHM, hCh0, hSh0, hH0]
      have hc2b : |c2| ≤ (Ch * (5124 / 10 ^ 4) + Sh / 100) / 2 ^ 53 + 1 / 2 ^ 1058 := by
        linarith only [hC3a, hDS, hDS2, hc1b, hCh0, hSh0]
      -- `sh ≤ 2.2358 |r1|`, and the low part of `R`
      have hr1lo2 : Sh ≤ |r1| * (1 + 1 / 2 ^ 52) + |c1| := by linarith only [hr1lo, hft, hr10]
      have hSr : Sh ≤ 22358 / 10 ^ 4 * |r1| + 1 / 2 ^ 1050 := by
        linarith only [hr1lo2, hc1b, hCh, hr10, hSh0]
      have hr1low : 1 / 2 ^ 62 ≤ |r1| := by linarith only [hSr, h1]
      have k9 : 2 ^ 53 * |r2| ≤ 64 * |r1| := by
        linarith only [hRlow, h2, hc2b, hCh, hSr, hr1low, hr10, hCh0, hSh0, hvl0]
      linarith only [k9]


#print axioms stepA
#print axioms stepB
#print axioms stepC
#print axioms combine_c2
#print axioms combine_r

end Verified.Examples.LgammaSinAccTail
