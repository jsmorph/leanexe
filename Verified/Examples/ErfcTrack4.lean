import Verified.Examples.ErfcTrack3

/-!
The double-double operations of `exp_1`, `q_1`, and `erfc_asympt_fast`, in the form of
`ErfcTrack`.  `pr_dMul` is `Erfc.dMul`, the product of two double-doubles without the product of
the low parts, `pr_sMul` is `Erfc.sMul`, a float times a double-double, and `fts_any` bounds
`fast_two_sum` without the condition on the order of its operands, whose error is then at most
about `u |b|`.
-/

namespace Verified.Examples.ErfcTrack4

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcEft2 ErfcTrack ErfcTrack2 FmaSpec

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

theorem dMul_eq (ah al bh bl : Float) :
    Erfc.dMul ah al bh bl = ((Erfc.aMul ah bh).1,
      Fma.fma al bh (Fma.fma ah bl (Erfc.aMul ah bh).2)) := rfl

theorem sMul_eq (a bh bl : Float) :
    Erfc.sMul a bh bl = ((Erfc.aMul a bh).1, Fma.fma a bl (Erfc.aMul a bh).2) := rfl

/-- The product of two double-doubles by `Erfc.dMul`. -/
theorem pr_dMul (hF : FmaNearest) {ah al bh bl : Float} {A B MA LA eA MB LB eB : ℝ}
    (ha : Pr ah al A MA LA eA) (hb : Pr bh bl B MB LB eB) (HA HB Ttl F1 M' L' e' : ℝ)
    (hHA : MA + eA + LA ≤ HA) (hHB : MB + eB + LB ≤ HB)
    (hTtl : u * u * (HA * HB) + 2 * η + (u * (HA * HB) + η) ≤ Ttl)
    (hF1 : (HA * LB + Ttl) * (1 + u) + η ≤ F1) (hM : MA * MB ≤ M')
    (hL : (LA * HB + F1) * (1 + u) + η ≤ L')
    (he : (MA + eA) * eB + MB * eA + LA * LB + (u * u * (HA * HB) + 2 * η) +
      (u * (HA * LB + Ttl) + η) + (u * (LA * HB + F1) + η) ≤ e')
    (hov : HA * HB + HA * LB + LA * HB + Ttl + F1 ≤ 2 ^ 1000) :
    Pr (Erfc.dMul ah al bh bl).1 (Erfc.dMul ah al bh bl).2 (A * B) M' L' e' := by
  rw [dMul_eq]
  have hHA' : |fv ah| ≤ HA := ha.h_le.trans hHA
  have hHB' : |fv bh| ≤ HB := hb.h_le.trans hHB
  have hHA0 : 0 ≤ HA := (abs_nonneg _).trans hHA'
  have hHB0 : 0 ≤ HB := (abs_nonneg _).trans hHB'
  have hLA0 := ha.L_nonneg
  have hLB0 := hb.L_nonneg
  have heA0 := ha.e_nonneg
  have heB0 := hb.e_nonneg
  have hMA0 := ha.M_nonneg
  have hMB0 := hb.M_nonneg
  have hu : (0 : ℝ) ≤ u := by positivity
  have hη : (0 : ℝ) ≤ η := by positivity
  have hHH : 0 ≤ HA * HB := mul_nonneg hHA0 hHB0
  have hHL : 0 ≤ HA * LB := mul_nonneg hHA0 hLB0
  have hLH : 0 ≤ LA * HB := mul_nonneg hLA0 hHB0
  obtain ⟨m1, m2, -, mtl, msum⟩ := amul_bound hF ha.1 hb.1 hHA' hHB' (by linarith)
  have htl : |fv (Erfc.aMul ah bh).2| ≤ Ttl := mtl.trans hTtl
  have hTtl0 : 0 ≤ Ttl := (abs_nonneg _).trans htl
  obtain ⟨w1, werr, wmag⟩ := fma_bound hF ha.1 hb.2.1 m2 hHA' hb.2.2.2.2 htl (by linarith)
  have hw : |fv (Fma.fma ah bl (Erfc.aMul ah bh).2)| ≤ F1 := wmag.trans hF1
  have hF10 : 0 ≤ F1 := (abs_nonneg _).trans hw
  obtain ⟨v1, verr, vmag⟩ := fma_bound hF ha.2.1 hb.1 w1 ha.2.2.2.2 hHB' hw (by linarith)
  refine ⟨m1, v1, ?_, ?_, vmag.trans hL⟩
  · set th := fv (Erfc.aMul ah bh).1
    set tl := fv (Erfc.aMul ah bh).2
    set f1 := fv (Fma.fma ah bl (Erfc.aMul ah bh).2)
    set f2 := fv (Fma.fma al bh (Fma.fma ah bl (Erfc.aMul ah bh).2))
    have e1 : th + f2 - A * B = (th + tl - fv ah * fv bh) + (f1 - (fv ah * fv bl + tl)) +
        (f2 - (fv al * fv bh + f1)) - fv al * fv bl +
        ((fv ah + fv al) * (fv bh + fv bl - B) + B * (fv ah + fv al - A)) := by ring
    rw [e1]
    have k1 : |(fv ah + fv al) * (fv bh + fv bl - B)| ≤ (MA + eA) * eB := by
      rw [abs_mul]
      refine mul_le_mul ?_ hb.2.2.1 (abs_nonneg _) (by linarith)
      have := abs_sub_abs_le_abs_sub (fv ah + fv al) A
      linarith [ha.2.2.1, ha.2.2.2.1]
    have k2 : |B * (fv ah + fv al - A)| ≤ MB * eA := by
      rw [abs_mul]; exact mul_le_mul hb.2.2.2.1 ha.2.2.1 (abs_nonneg _) hMB0
    have k3 : |fv al * fv bl| ≤ LA * LB := by
      rw [abs_mul]; exact mul_le_mul ha.2.2.2.2 hb.2.2.2.2 (abs_nonneg _) hLA0
    have t1 := abs_add3 (th + tl - fv ah * fv bh) (f1 - (fv ah * fv bl + tl))
      (f2 - (fv al * fv bh + f1))
    have t2 := abs_sub_le' (th + tl - fv ah * fv bh + (f1 - (fv ah * fv bl + tl)) +
      (f2 - (fv al * fv bh + f1))) (fv al * fv bl)
    have t3 := abs_add_le (th + tl - fv ah * fv bh + (f1 - (fv ah * fv bl + tl)) +
      (f2 - (fv al * fv bh + f1)) - fv al * fv bl)
      ((fv ah + fv al) * (fv bh + fv bl - B) + B * (fv ah + fv al - A))
    have t4 := abs_add_le ((fv ah + fv al) * (fv bh + fv bl - B)) (B * (fv ah + fv al - A))
    linarith
  · rw [abs_mul]
    exact (mul_le_mul ha.2.2.2.1 hb.2.2.2.1 (abs_nonneg _) hMA0).trans hM

/-- `fast_two_sum` without the condition on its operands: for `|a| ≤ A` and `|b| ≤ B` the computed
pair lies within `2 u B + 3 u² (A + B)` of `a + b`. -/
theorem fts_any {a b : Float} {A B : ℝ} (ha : ff a) (hb : ff b) (hA : |fv a| ≤ A)
    (hB : |fv b| ≤ B) (hov : A + B ≤ 2 ^ 1000) :
    ff (Erfc.fastTwoSum a b).1 ∧ ff (Erfc.fastTwoSum a b).2 ∧
      |fv (Erfc.fastTwoSum a b).1 + fv (Erfc.fastTwoSum a b).2 - (fv a + fv b)| ≤
        2 * u * B + 3 * u * u * (A + B) ∧
      |fv (Erfc.fastTwoSum a b).2| ≤ 4 * u * (A + B) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hu : (0 : ℝ) ≤ u := by positivity
  have hu1 : u ≤ 1 / 4 := by norm_num
  obtain ⟨s1, serr, smag⟩ := add_bound ha hb hA hB hov
  -- `z = s - a`
  have hsa : |fv (a + b) - fv a| ≤ B + u * (A + B) := by
    have : fv (a + b) - fv a = fv b + (fv (a + b) - (fv a + fv b)) := by ring
    rw [this]; exact (abs_add_le _ _).trans (by linarith)
  have hsa' : |fv (a + b) - fv a| ≤ 2 ^ 1022 := hsa.trans (by
    have : u * (A + B) ≤ A + B := by nlinarith
    linarith [show (2 : ℝ) ^ 1000 ≤ 2 ^ 1022 by norm_num])
  obtain ⟨z1, zerr⟩ := sub_f (a + b) a s1 ha hsa'
  have hzerr : |fv (a + b - a) - (fv (a + b) - fv a)| ≤ u * (B + u * (A + B)) :=
    zerr.trans (by gcongr)
  -- `t = b - z`
  have hbz : |fv b - fv (a + b - a)| ≤ u * (A + B) + u * (B + u * (A + B)) := by
    have : fv b - fv (a + b - a) = -(fv (a + b) - (fv a + fv b)) -
        (fv (a + b - a) - (fv (a + b) - fv a)) := by ring
    rw [this]
    exact (abs_sub_le' _ _).trans (by rw [abs_neg]; linarith)
  have hbz' : |fv b - fv (a + b - a)| ≤ 2 ^ 1022 := hbz.trans (by
    have : u * (A + B) ≤ A + B := by nlinarith
    have : u * (B + u * (A + B)) ≤ B + (A + B) := by nlinarith
    linarith [show (2 : ℝ) ^ 1000 ≤ 2 ^ 1022 by norm_num])
  obtain ⟨t1, terr⟩ := sub_f b (a + b - a) hb z1 hbz'
  have hfst : (Erfc.fastTwoSum a b).1 = a + b := rfl
  have hsnd : (Erfc.fastTwoSum a b).2 = b - (a + b - a) := rfl
  rw [hfst, hsnd]
  refine ⟨s1, t1, ?_, ?_⟩
  · have e1 : fv (a + b) + fv (b - (a + b - a)) - (fv a + fv b) =
        -(fv (a + b - a) - (fv (a + b) - fv a)) +
          (fv (b - (a + b - a)) - (fv b - fv (a + b - a))) := by ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    have k : u * |fv b - fv (a + b - a)| ≤ u * (u * (A + B) + u * (B + u * (A + B))) := by gcongr
    have f1 : u * u * B ≤ u * B := by nlinarith
    have f2 : u * u * u * (A + B) ≤ u * u * (A + B) := by nlinarith [mul_nonneg hu hu]
    calc |fv (a + b - a) - (fv (a + b) - fv a)| + |fv (b - (a + b - a)) - (fv b - fv (a + b - a))|
        ≤ u * (B + u * (A + B)) + u * (u * (A + B) + u * (B + u * (A + B))) :=
          add_le_add hzerr (terr.trans k)
      _ ≤ 2 * u * B + 3 * u * u * (A + B) := by linarith [f1, f2]
  · have := abs_sub_abs_le_abs_sub (fv (b - (a + b - a))) (fv b - fv (a + b - a))
    have k : u * |fv b - fv (a + b - a)| ≤ u * (u * (A + B) + u * (B + u * (A + B))) := by gcongr
    nlinarith

/-- A float times a double-double by `Erfc.sMul`: `aMul a bh` with `a bl` added to its error term by
one `fma`. -/
theorem pr_sMul (hF : FmaNearest) {a bh bl : Float} {va B Ma ea MB LB eB : ℝ}
    (ha : Tr a va Ma ea) (hb : Pr bh bl B MB LB eB) (HA HB Ttl M' L' e' : ℝ)
    (hHA : Ma + ea ≤ HA) (hHB : MB + eB + LB ≤ HB)
    (hTtl : u * u * (HA * HB) + 2 * η + (u * (HA * HB) + η) ≤ Ttl) (hM : Ma * MB ≤ M')
    (hL : (HA * LB + Ttl) * (1 + u) + η ≤ L')
    (he : (Ma + ea) * eB + MB * ea + (u * u * (HA * HB) + 2 * η) + (u * (HA * LB + Ttl) + η) ≤ e')
    (hov : HA * HB + HA * LB + Ttl ≤ 2 ^ 1000) :
    Pr (Erfc.sMul a bh bl).1 (Erfc.sMul a bh bl).2 (va * B) M' L' e' := by
  rw [sMul_eq]
  have hHA' : |fv a| ≤ HA := ha.abs_le.trans hHA
  have hHB' : |fv bh| ≤ HB := hb.h_le.trans hHB
  have hHA0 : 0 ≤ HA := (abs_nonneg _).trans hHA'
  have hHB0 : 0 ≤ HB := (abs_nonneg _).trans hHB'
  have hLB0 := hb.L_nonneg
  have heB0 := hb.e_nonneg
  have hMB0 := hb.M_nonneg
  have hea := ha.e_nonneg
  have hMa := ha.M_nonneg
  have hu : (0 : ℝ) ≤ u := by positivity
  have hη : (0 : ℝ) ≤ η := by positivity
  have hHH : 0 ≤ HA * HB := mul_nonneg hHA0 hHB0
  have hHL : 0 ≤ HA * LB := mul_nonneg hHA0 hLB0
  obtain ⟨m1, m2, -, mtl, msum⟩ := amul_bound hF ha.1 hb.1 hHA' hHB' (by linarith)
  have htl : |fv (Erfc.aMul a bh).2| ≤ Ttl := mtl.trans hTtl
  have hTtl0 : 0 ≤ Ttl := (abs_nonneg _).trans htl
  obtain ⟨w1, werr, wmag⟩ := fma_bound hF ha.1 hb.2.1 m2 hHA' hb.2.2.2.2 htl (by linarith)
  refine ⟨m1, w1, ?_, ?_, wmag.trans hL⟩
  · set th := fv (Erfc.aMul a bh).1
    set tl := fv (Erfc.aMul a bh).2
    set f1 := fv (Fma.fma a bl (Erfc.aMul a bh).2)
    have e1 : th + f1 - va * B = (th + tl - fv a * fv bh) + (f1 - (fv a * fv bl + tl)) +
        (fv a * (fv bh + fv bl - B) + B * (fv a - va)) := by ring
    rw [e1]
    have k1 : |fv a * (fv bh + fv bl - B)| ≤ (Ma + ea) * eB := by
      rw [abs_mul]; exact mul_le_mul ha.abs_le hb.2.2.1 (abs_nonneg _) (by linarith)
    have k2 : |B * (fv a - va)| ≤ MB * ea := by
      rw [abs_mul]; exact mul_le_mul hb.2.2.2.1 ha.2.1 (abs_nonneg _) hMB0
    have t1 := abs_add3 (th + tl - fv a * fv bh) (f1 - (fv a * fv bl + tl))
      (fv a * (fv bh + fv bl - B) + B * (fv a - va))
    have t2 := abs_add_le (fv a * (fv bh + fv bl - B)) (B * (fv a - va))
    linarith
  · rw [abs_mul]
    exact (mul_le_mul ha.2.2 hb.2.2.2.1 (abs_nonneg _) hMa).trans hM

theorem fastSum_eq (a bh bl : Float) :
    Erfc.fastSum a bh bl = ((Erfc.fastTwoSum a bh).1, (Erfc.fastTwoSum a bh).2 + bl) := rfl

/-- `Erfc.fastSum`: `c + (h, l)` by `fast_two_sum (c, h)` with `l` added to its error term. -/
theorem pr_fastSum {c h l : Float} {V M L e Mc mc : ℝ} (hc : ff c) (hMc : |fv c| ≤ Mc)
    (hmc : mc ≤ |fv c|) (hp : Pr h l V M L e) (H M' L' e' T : ℝ) (hH : M + e + L ≤ H)
    (hpre : H ≤ mc) (hT : u * (Mc + H) ≤ T) (hM : Mc + M ≤ M') (hL : (T + L) * (1 + u) ≤ L')
    (he : e + u * (T + L) ≤ e') (hov : Mc + H + L + T ≤ 2 ^ 1000) :
    Pr (Erfc.fastSum c h l).1 (Erfc.fastSum c h l).2 (fv c + V) M' L' e' := by
  rw [fastSum_eq]
  have hhH : |fv h| ≤ H := hp.h_le.trans hH
  have hL0 := hp.L_nonneg
  have he0 := hp.e_nonneg
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hhH
  have hMc0 : 0 ≤ Mc := (abs_nonneg _).trans hMc
  obtain ⟨f1, f2, fsum, ft⟩ := fts_bound hc hp.1 hMc hhH (hhH.trans (hpre.trans hmc))
    (by linarith)
  have hT' : |fv (Erfc.fastTwoSum c h).2| ≤ T := ft.trans hT
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT'
  obtain ⟨s1, serr, smag⟩ := add_bound f2 hp.2.1 hT' hp.2.2.2.2 (by linarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · have e1 : fv (Erfc.fastTwoSum c h).1 + fv ((Erfc.fastTwoSum c h).2 + l) - (fv c + V) =
        (fv h + fv l - V) +
          (fv ((Erfc.fastTwoSum c h).2 + l) - (fv (Erfc.fastTwoSum c h).2 + fv l)) := by
      linarith
    rw [e1]
    exact (abs_add_le _ _).trans (by linarith [hp.2.2.1])
  · exact (abs_add_le _ _).trans (by linarith [hp.2.2.2.1])

/-- `(c + d) + (h, l)` by `fast_two_sum (c, h)` with `l + d` added to its error term. -/
theorem pr_fastSumB {c d h l : Float} {V M L e Mc mc Md : ℝ} (hc : ff c) (hMc : |fv c| ≤ Mc)
    (hmc : mc ≤ |fv c|) (hd : ff d) (hMd : |fv d| ≤ Md) (hp : Pr h l V M L e)
    (H M' L' e' T Vb : ℝ) (hH : M + e + L ≤ H) (hpre : H ≤ mc) (hT : u * (Mc + H) ≤ T)
    (hVb : (L + Md) * (1 + u) ≤ Vb) (hM : Mc + Md + M ≤ M') (hL : (T + Vb) * (1 + u) ≤ L')
    (he : e + u * (L + Md) + u * (T + Vb) ≤ e') (hov : Mc + H + L + Md + T + Vb ≤ 2 ^ 1000) :
    Pr (Erfc.fastTwoSum c h).1 ((Erfc.fastTwoSum c h).2 + (l + d)) (fv c + fv d + V) M' L' e' := by
  have hhH : |fv h| ≤ H := hp.h_le.trans hH
  have hL0 := hp.L_nonneg
  have he0 := hp.e_nonneg
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hhH
  have hMc0 : 0 ≤ Mc := (abs_nonneg _).trans hMc
  have hMd0 : 0 ≤ Md := (abs_nonneg _).trans hMd
  obtain ⟨f1, f2, fsum, ft⟩ := fts_bound hc hp.1 hMc hhH (hhH.trans (hpre.trans hmc))
    (by linarith)
  have hT' : |fv (Erfc.fastTwoSum c h).2| ≤ T := ft.trans hT
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT'
  obtain ⟨v1, verr, vmag⟩ := add_bound hp.2.1 hd hp.2.2.2.2 hMd (by linarith)
  have hv : |fv (l + d)| ≤ Vb := vmag.trans hVb
  have hVb0 : 0 ≤ Vb := (abs_nonneg _).trans hv
  obtain ⟨s1, serr, smag⟩ := add_bound f2 v1 hT' hv (by linarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · have e1 : fv (Erfc.fastTwoSum c h).1 + fv ((Erfc.fastTwoSum c h).2 + (l + d)) -
        (fv c + fv d + V) = (fv h + fv l - V) + (fv (l + d) - (fv l + fv d)) +
          (fv ((Erfc.fastTwoSum c h).2 + (l + d)) - (fv (Erfc.fastTwoSum c h).2 + fv (l + d))) := by
      linarith
    rw [e1]
    exact (abs_add3 _ _ _).trans (by linarith [hp.2.2.1])
  · refine (abs_add_le _ _).trans ?_
    have := abs_add_le (fv c) (fv d)
    linarith [hp.2.2.2.1]

#print axioms pr_fastSumB
#print axioms pr_sMul
#print axioms pr_fastSum

#print axioms pr_dMul
#print axioms fts_any

end Verified.Examples.ErfcTrack4
