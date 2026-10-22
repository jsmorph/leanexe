import Library.Numerics.Float64.Erfc.ErfcTrack2

/-!
The stages of `cr_erf_accurate` and its tiny case, in the form of `ErfcTrack`.  `pr_twoS` and
`pr_twoT` are the steps of `cr_erf_accurate`'s second and third loops: a double-double times an
exact float `z` by `Erfc.aMul` and one `fma`, plus a coefficient by `Erfc.twoSum`, which is exact
without a condition on the operands' order.  `pr_coefA` and `pr_coefB` add a coefficient to a
double-double by `fast_two_sum`, as `cr_erf_accurate_tiny`'s loops do after `mulZ2`, which is
`ErfcTrack2.pr_mulG` twice.
-/

namespace Library.Numerics.Float64.Erfc.ErfcTrack3

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcEft2 ErfcTrack ErfcTrack2 Library.Numerics.Arithmetic.Fma.FmaSpec

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

/-- `Erfc.twoSum a b` for bounded operands: the exact sum and the bound on the error term. -/
theorem two_bound {a b : Float} {A B : ℝ} (ha : ff a) (hb : ff b) (hA : |fv a| ≤ A)
    (hB : |fv b| ≤ B) (hov : A + B ≤ 2 ^ 1000) :
    ff (Erfc.twoSum a b).1 ∧ ff (Erfc.twoSum a b).2 ∧
      fv (Erfc.twoSum a b).1 + fv (Erfc.twoSum a b).2 = fv a + fv b ∧
      |fv (Erfc.twoSum a b).2| ≤ u * (A + B) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have k : (2 : ℝ) ^ 1000 ≤ 2 ^ 1018 := by norm_num
  obtain ⟨h1, h2, hsum, -, -⟩ := twoSum_f a b ha hb (by linarith) (by linarith)
  obtain ⟨-, herr, -⟩ := add_bound ha hb hA hB hov
  refine ⟨h1, h2, hsum, ?_⟩
  have hf : (Erfc.twoSum a b).1 = a + b := rfl
  have ht : fv (Erfc.twoSum a b).2 = -(fv (a + b) - (fv a + fv b)) := by
    rw [← hf]; linarith
  rw [ht, abs_neg]
  exact herr

/-- `c + (h, l) z` in the order of `cr_erf_accurate`'s second loop. -/
theorem pr_twoS (hF : FmaNearest) {z c h l : Float} {V M L e R Mc : ℝ} (hz : ff z)
    (hzR : |fv z| ≤ R) (hc : ff c) (hMc : |fv c| ≤ Mc) (hp : Pr h l V M L e)
    (H Th Ttl W M' L' e' : ℝ) (hH : M + e + L ≤ H)
    (hTh : H * R * (1 + u) + η ≤ Th)
    (hTtl : u * u * (H * R) + 2 * η + (u * (H * R) + η) ≤ Ttl)
    (hW : (L * R + Ttl) * (1 + u) + η ≤ W) (hM : Mc + M * R ≤ M')
    (hL : (u * (Mc + Th) + W) * (1 + u) ≤ L')
    (he : R * e + (u * u * (H * R) + 2 * η) + (u * (L * R + Ttl) + η) +
      u * (u * (Mc + Th) + W) ≤ e')
    (hov : Mc + Th + H * R + L * R + Ttl + W ≤ 2 ^ 1000) :
    Pr (Erfc.twoSum c (Erfc.aMul h z).1).1
      ((Erfc.twoSum c (Erfc.aMul h z).1).2 + Library.Numerics.Arithmetic.Fma.Fma.fma l z (Erfc.aMul h z).2)
      (fv c + V * fv z) M' L' e' := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hzR
  have hL0 := hp.L_nonneg
  have hM0 := hp.M_nonneg
  have he0 := hp.e_nonneg
  have hMc0 : 0 ≤ Mc := (abs_nonneg _).trans hMc
  have hhH : |fv h| ≤ H := hp.h_le.trans hH
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hhH
  have hHR : 0 ≤ H * R := mul_nonneg hH0 hR0
  have hLR : 0 ≤ L * R := mul_nonneg hL0 hR0
  have hu : (0 : ℝ) ≤ u := by positivity
  have hη : (0 : ℝ) ≤ η := by positivity
  obtain ⟨m1, m2, mth, mtl, msum⟩ := amul_bound hF hp.1 hz hhH hzR (by linarith)
  have hth : |fv (Erfc.aMul h z).1| ≤ Th := mth.trans hTh
  have htl : |fv (Erfc.aMul h z).2| ≤ Ttl := mtl.trans hTtl
  have hTh0 : 0 ≤ Th := (abs_nonneg _).trans hth
  have hTtl0 : 0 ≤ Ttl := (abs_nonneg _).trans htl
  obtain ⟨f1, f2, fsum, ft⟩ := two_bound hc m1 hMc hth (by linarith)
  obtain ⟨w1, werr, wmag⟩ := fma_bound hF hp.2.1 hz m2 hp.2.2.2.2 hzR htl (by linarith)
  have hw : |fv (Library.Numerics.Arithmetic.Fma.Fma.fma l z (Erfc.aMul h z).2)| ≤ W := wmag.trans hW
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hw
  have hut : u * (Mc + Th) ≤ Mc + Th := by
    have : u ≤ 1 := by norm_num
    nlinarith
  obtain ⟨s1, serr, smag⟩ := add_bound f2 w1 ft hw (by linarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · set th := fv (Erfc.aMul h z).1
    set tl := fv (Erfc.aMul h z).2
    set t := fv (Erfc.twoSum c (Erfc.aMul h z).1).2
    set w := fv (Library.Numerics.Arithmetic.Fma.Fma.fma l z (Erfc.aMul h z).2)
    set lo := fv ((Erfc.twoSum c (Erfc.aMul h z).1).2 + Library.Numerics.Arithmetic.Fma.Fma.fma l z (Erfc.aMul h z).2)
    have e1 : fv (Erfc.twoSum c (Erfc.aMul h z).1).1 + lo - (fv c + V * fv z) =
        (th + tl - fv h * fv z) + (w - (fv l * fv z + tl)) + (lo - (t + w)) +
          fv z * (fv h + fv l - V) := by
      linear_combination fsum
    rw [e1]
    have hzV : |fv z * (fv h + fv l - V)| ≤ R * e := by
      rw [abs_mul]; exact mul_le_mul hzR hp.2.2.1 (abs_nonneg _) hR0
    have k1 := abs_add3 (th + tl - fv h * fv z) (w - (fv l * fv z + tl)) (lo - (t + w))
    have k2 := abs_add_le (th + tl - fv h * fv z + (w - (fv l * fv z + tl)) + (lo - (t + w)))
      (fv z * (fv h + fv l - V))
    linarith
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul hp.2.2.2.1 hzR (abs_nonneg _) hM0
    linarith

/-- `(c + d) + (h, l) z` in the order of `cr_erf_accurate`'s third loop. -/
theorem pr_twoT (hF : FmaNearest) {z c d h l : Float} {V M L e R Mc Md : ℝ} (hz : ff z)
    (hzR : |fv z| ≤ R) (hc : ff c) (hMc : |fv c| ≤ Mc) (hd : ff d) (hMd : |fv d| ≤ Md)
    (hp : Pr h l V M L e) (H Th Ttl W Vb M' L' e' : ℝ) (hH : M + e + L ≤ H)
    (hTh : H * R * (1 + u) + η ≤ Th)
    (hTtl : u * u * (H * R) + 2 * η + (u * (H * R) + η) ≤ Ttl)
    (hW : (L * R + Ttl) * (1 + u) + η ≤ W) (hVb : (Md + W) * (1 + u) ≤ Vb)
    (hM : Mc + Md + M * R ≤ M') (hL : (u * (Mc + Th) + Vb) * (1 + u) ≤ L')
    (he : R * e + (u * u * (H * R) + 2 * η) + (u * (L * R + Ttl) + η) + u * (Md + W) +
      u * (u * (Mc + Th) + Vb) ≤ e')
    (hov : Mc + Th + H * R + L * R + Md + Ttl + W + Vb ≤ 2 ^ 1000) :
    Pr (Erfc.twoSum c (Erfc.aMul h z).1).1
      ((Erfc.twoSum c (Erfc.aMul h z).1).2 + (d + Library.Numerics.Arithmetic.Fma.Fma.fma l z (Erfc.aMul h z).2))
      (fv c + fv d + V * fv z) M' L' e' := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hzR
  have hL0 := hp.L_nonneg
  have hM0 := hp.M_nonneg
  have he0 := hp.e_nonneg
  have hMc0 : 0 ≤ Mc := (abs_nonneg _).trans hMc
  have hMd0 : 0 ≤ Md := (abs_nonneg _).trans hMd
  have hhH : |fv h| ≤ H := hp.h_le.trans hH
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hhH
  have hHR : 0 ≤ H * R := mul_nonneg hH0 hR0
  have hLR : 0 ≤ L * R := mul_nonneg hL0 hR0
  have hu : (0 : ℝ) ≤ u := by positivity
  have hη : (0 : ℝ) ≤ η := by positivity
  obtain ⟨m1, m2, mth, mtl, msum⟩ := amul_bound hF hp.1 hz hhH hzR (by linarith)
  have hth : |fv (Erfc.aMul h z).1| ≤ Th := mth.trans hTh
  have htl : |fv (Erfc.aMul h z).2| ≤ Ttl := mtl.trans hTtl
  have hTh0 : 0 ≤ Th := (abs_nonneg _).trans hth
  have hTtl0 : 0 ≤ Ttl := (abs_nonneg _).trans htl
  obtain ⟨f1, f2, fsum, ft⟩ := two_bound hc m1 hMc hth (by linarith)
  obtain ⟨w1, werr, wmag⟩ := fma_bound hF hp.2.1 hz m2 hp.2.2.2.2 hzR htl (by linarith)
  have hw : |fv (Library.Numerics.Arithmetic.Fma.Fma.fma l z (Erfc.aMul h z).2)| ≤ W := wmag.trans hW
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hw
  obtain ⟨v1, verr, vmag⟩ := add_bound hd w1 hMd hw (by linarith)
  have hv : |fv (d + Library.Numerics.Arithmetic.Fma.Fma.fma l z (Erfc.aMul h z).2)| ≤ Vb := vmag.trans hVb
  have hVb0 : 0 ≤ Vb := (abs_nonneg _).trans hv
  have hut : u * (Mc + Th) ≤ Mc + Th := by
    have : u ≤ 1 := by norm_num
    nlinarith
  obtain ⟨s1, serr, smag⟩ := add_bound f2 v1 ft hv (by linarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · set th := fv (Erfc.aMul h z).1
    set tl := fv (Erfc.aMul h z).2
    set t := fv (Erfc.twoSum c (Erfc.aMul h z).1).2
    set w := fv (Library.Numerics.Arithmetic.Fma.Fma.fma l z (Erfc.aMul h z).2)
    set v := fv (d + Library.Numerics.Arithmetic.Fma.Fma.fma l z (Erfc.aMul h z).2)
    set lo := fv ((Erfc.twoSum c (Erfc.aMul h z).1).2 + (d + Library.Numerics.Arithmetic.Fma.Fma.fma l z (Erfc.aMul h z).2))
    have e1 : fv (Erfc.twoSum c (Erfc.aMul h z).1).1 + lo - (fv c + fv d + V * fv z) =
        (th + tl - fv h * fv z) + (w - (fv l * fv z + tl)) + (v - (fv d + w)) + (lo - (t + v)) +
          fv z * (fv h + fv l - V) := by
      linear_combination fsum
    rw [e1]
    have hzV : |fv z * (fv h + fv l - V)| ≤ R * e := by
      rw [abs_mul]; exact mul_le_mul hzR hp.2.2.1 (abs_nonneg _) hR0
    have k1 := abs_add3 (th + tl - fv h * fv z) (w - (fv l * fv z + tl)) (v - (fv d + w))
    have k2 := abs_add3 (th + tl - fv h * fv z + (w - (fv l * fv z + tl)) + (v - (fv d + w)))
      (lo - (t + v)) (fv z * (fv h + fv l - V))
    linarith
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul hp.2.2.2.1 hzR (abs_nonneg _) hM0
    have := abs_add_le (fv c) (fv d)
    linarith

/-- `c + (h, l)`: `fast_two_sum (c, h)` with its error term added to `l`. -/
theorem pr_coefA {c h l : Float} {V M L e Mc mc : ℝ} (hc : ff c) (hMc : |fv c| ≤ Mc)
    (hmc : mc ≤ |fv c|) (hp : Pr h l V M L e) (H M' L' e' T : ℝ) (hH : M + e + L ≤ H)
    (hpre : H ≤ mc) (hT : u * (Mc + H) ≤ T) (hM : Mc + M ≤ M') (hL : (L + T) * (1 + u) ≤ L')
    (he : e + u * (L + T) ≤ e') (hov : Mc + H + L + T ≤ 2 ^ 1000) :
    Pr (Erfc.fastTwoSum c h).1 (l + (Erfc.fastTwoSum c h).2) (fv c + V) M' L' e' := by
  have hhH : |fv h| ≤ H := hp.h_le.trans hH
  have hL0 := hp.L_nonneg
  have he0 := hp.e_nonneg
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hhH
  have hMc0 : 0 ≤ Mc := (abs_nonneg _).trans hMc
  obtain ⟨f1, f2, fsum, ft⟩ := fts_bound hc hp.1 hMc hhH (hhH.trans (hpre.trans hmc))
    (by linarith)
  have hT' : |fv (Erfc.fastTwoSum c h).2| ≤ T := ft.trans hT
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT'
  obtain ⟨s1, serr, smag⟩ := add_bound hp.2.1 f2 hp.2.2.2.2 hT' (by linarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · have e1 : fv (Erfc.fastTwoSum c h).1 + fv (l + (Erfc.fastTwoSum c h).2) - (fv c + V) =
        (fv h + fv l - V) +
          (fv (l + (Erfc.fastTwoSum c h).2) - (fv l + fv (Erfc.fastTwoSum c h).2)) := by
      linarith
    rw [e1]
    exact (abs_add_le _ _).trans (by linarith [hp.2.2.1])
  · exact (abs_add_le _ _).trans (by linarith [hp.2.2.2.1])

/-- `(c + d) + (h, l)`: `fast_two_sum (c, h)` with `d` plus its error term added to `l`. -/
theorem pr_coefB {c d h l : Float} {V M L e Mc mc Md : ℝ} (hc : ff c) (hMc : |fv c| ≤ Mc)
    (hmc : mc ≤ |fv c|) (hd : ff d) (hMd : |fv d| ≤ Md) (hp : Pr h l V M L e)
    (H M' L' e' T Vb : ℝ) (hH : M + e + L ≤ H) (hpre : H ≤ mc) (hT : u * (Mc + H) ≤ T)
    (hVb : (Md + T) * (1 + u) ≤ Vb) (hM : Mc + Md + M ≤ M') (hL : (L + Vb) * (1 + u) ≤ L')
    (he : e + u * (Md + T) + u * (L + Vb) ≤ e') (hov : Mc + H + L + Md + T + Vb ≤ 2 ^ 1000) :
    Pr (Erfc.fastTwoSum c h).1 (l + (d + (Erfc.fastTwoSum c h).2)) (fv c + fv d + V) M' L' e' := by
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
  obtain ⟨v1, verr, vmag⟩ := add_bound hd f2 hMd hT' (by linarith)
  have hv : |fv (d + (Erfc.fastTwoSum c h).2)| ≤ Vb := vmag.trans hVb
  have hVb0 : 0 ≤ Vb := (abs_nonneg _).trans hv
  obtain ⟨s1, serr, smag⟩ := add_bound hp.2.1 v1 hp.2.2.2.2 hv (by linarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · have e1 : fv (Erfc.fastTwoSum c h).1 + fv (l + (d + (Erfc.fastTwoSum c h).2)) -
        (fv c + fv d + V) = (fv h + fv l - V) +
          (fv (d + (Erfc.fastTwoSum c h).2) - (fv d + fv (Erfc.fastTwoSum c h).2)) +
          (fv (l + (d + (Erfc.fastTwoSum c h).2)) - (fv l + fv (d + (Erfc.fastTwoSum c h).2))) := by
      linarith
    rw [e1]
    exact (abs_add3 _ _ _).trans (by linarith [hp.2.2.1])
  · refine (abs_add_le _ _).trans ?_
    have := abs_add_le (fv c) (fv d)
    linarith [hp.2.2.2.1]

#print axioms pr_twoS
#print axioms pr_twoT
#print axioms pr_coefA
#print axioms pr_coefB

end Library.Numerics.Float64.Erfc.ErfcTrack3
