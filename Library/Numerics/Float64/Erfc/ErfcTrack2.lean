import Library.Numerics.Float64.Erfc.ErfcTrack

/-!
The stages of `cr_erf_fast` below `1/16` (`Erfc.erfFastTiny`), in the form of `ErfcTrack`.  The
code evaluates its polynomial in `w`, the high part of `z²`, and adds the low part `z2l` of `z²`
once.  `pr_mulE` multiplies a float by `w` with `Erfc.aMul` and adds a double-double coefficient,
`pr_mulF` multiplies a double-double by `w + z2l` and adds a double-double coefficient, and
`pr_mulG` multiplies a double-double by `z` without a coefficient.
-/

namespace Library.Numerics.Float64.Erfc.ErfcTrack2

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcEft2 ErfcTrack Library.Numerics.Arithmetic.Fma.FmaSpec

set_option exponentiation.threshold 2200

/-- A rational inequality, cast to the reals: casts the hypothesis, pushes the casts in it and in
the goal, and closes the goal by `linarith`. -/
macro "qcast " h:term : tactic =>
  `(tactic| (have hq := (Rat.cast_le (K := ℝ)).mpr $h; push_cast at hq ⊢; linarith))

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

/-- `(a + b) + w p` for a float `p`: `aMul w p`, `fast_two_sum` with `a`, and the error term plus
`b` added to the low part. -/
theorem pr_mulE (hF : FmaNearest) {w p a b : Float} {vp Mp ep R Ma ma Mb : ℝ} (hw : ff w)
    (hwR : |fv w| ≤ R) (hp : Tr p vp Mp ep) (ha : ff a) (hMa : |fv a| ≤ Ma)
    (hma : ma ≤ |fv a|) (hb : ff b) (hMb : |fv b| ≤ Mb) (H Th Ttl Vb M' L' e' : ℝ)
    (hH : Mp + ep ≤ H) (hTh : R * H * (1 + u) + η ≤ Th) (hpre : Th ≤ ma)
    (hTtl : u * u * (R * H) + 2 * η + (u * (R * H) + η) ≤ Ttl)
    (hVb : (Ttl + Mb) * (1 + u) ≤ Vb) (hM : Ma + Mb + R * Mp ≤ M')
    (hL : (u * (Ma + Th) + Vb) * (1 + u) ≤ L')
    (he : R * ep + (u * u * (R * H) + 2 * η) + u * (Ttl + Mb) + u * (u * (Ma + Th) + Vb) ≤ e')
    (hov : Ma + Th + R * H + Mb + Ttl + Vb ≤ 2 ^ 1000) :
    Pr (Erfc.fastTwoSum a (Erfc.aMul w p).1).1
      ((Erfc.fastTwoSum a (Erfc.aMul w p).1).2 + ((Erfc.aMul w p).2 + b))
      (fv a + fv b + fv w * vp) M' L' e' := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hwR
  have hpH : |fv p| ≤ H := hp.abs_le.trans hH
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hpH
  have hRH : 0 ≤ R * H := mul_nonneg hR0 hH0
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans hMb
  have hMa0 : 0 ≤ Ma := (abs_nonneg _).trans hMa
  have hep := hp.e_nonneg
  have hu : (0 : ℝ) ≤ u := by positivity
  have hη : (0 : ℝ) ≤ η := by positivity
  obtain ⟨m1, m2, mth, mtl, msum⟩ := amul_bound hF hw hp.1 hwR hpH (by linarith)
  have hth : |fv (Erfc.aMul w p).1| ≤ Th := mth.trans hTh
  have htl : |fv (Erfc.aMul w p).2| ≤ Ttl := mtl.trans hTtl
  have hTh0 : 0 ≤ Th := (abs_nonneg _).trans hth
  have hTtl0 : 0 ≤ Ttl := (abs_nonneg _).trans htl
  obtain ⟨f1, f2, fsum, ft⟩ := fts_bound ha m1 hMa hth (hth.trans (hpre.trans hma))
    (by linarith)
  obtain ⟨v1, verr, vmag⟩ := add_bound m2 hb htl hMb (by linarith)
  have hv : |fv ((Erfc.aMul w p).2 + b)| ≤ Vb := vmag.trans hVb
  have hVb0 : 0 ≤ Vb := (abs_nonneg _).trans hv
  have hut : u * (Ma + Th) ≤ Ma + Th := by
    have : u ≤ 1 := by norm_num
    nlinarith
  obtain ⟨s1, serr, smag⟩ := add_bound f2 v1 ft hv (by linarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · set th := fv (Erfc.aMul w p).1
    set tl := fv (Erfc.aMul w p).2
    set t := fv (Erfc.fastTwoSum a (Erfc.aMul w p).1).2
    set v := fv ((Erfc.aMul w p).2 + b)
    set lo := fv ((Erfc.fastTwoSum a (Erfc.aMul w p).1).2 + ((Erfc.aMul w p).2 + b))
    have e1 : fv (Erfc.fastTwoSum a (Erfc.aMul w p).1).1 + lo - (fv a + fv b + fv w * vp) =
        (th + tl - fv w * fv p) + (v - (tl + fv b)) + (lo - (t + v)) + fv w * (fv p - vp) := by
      linear_combination fsum
    rw [e1]
    have hwp : |fv w * (fv p - vp)| ≤ R * ep := by
      rw [abs_mul]; exact mul_le_mul hwR hp.2.1 (abs_nonneg _) hR0
    have k1 := abs_add3 (th + tl - fv w * fv p) (v - (tl + fv b)) (lo - (t + v))
    have k2 := abs_add_le (th + tl - fv w * fv p + (v - (tl + fv b)) + (lo - (t + v)))
      (fv w * (fv p - vp))
    linarith
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul hwR hp.2.2 (abs_nonneg _) hR0
    have := abs_add_le (fv a) (fv b)
    linarith

set_option maxHeartbeats 1000000 in
/-- `(a + b) + (w + y) (h, l)`: `aMul w h`, `w l + b` by one `fma` added to its error term,
`fast_two_sum` with `a`, and `y h` plus that sum by one `fma` added to the low part. -/
theorem pr_mulF (hF : FmaNearest) {w y a b h l : Float} {V M L e R Y Ma ma Mb : ℝ} (hw : ff w)
    (hwR : |fv w| ≤ R) (hy : ff y) (hyY : |fv y| ≤ Y) (ha : ff a) (hMa : |fv a| ≤ Ma)
    (hma : ma ≤ |fv a|) (hb : ff b) (hMb : |fv b| ≤ Mb) (hp : Pr h l V M L e)
    (H Th Ttl W1 T1 W2 M' L' e' : ℝ) (hH : M + e + L ≤ H)
    (hTh : R * H * (1 + u) + η ≤ Th) (hpre : Th ≤ ma)
    (hTtl : u * u * (R * H) + 2 * η + (u * (R * H) + η) ≤ Ttl)
    (hW1 : (R * L + Mb) * (1 + u) + η ≤ W1) (hT1 : (Ttl + W1) * (1 + u) ≤ T1)
    (hW2 : (Y * H + T1) * (1 + u) + η ≤ W2) (hM : Ma + Mb + (R + Y) * M ≤ M')
    (hL : (u * (Ma + Th) + W2) * (1 + u) ≤ L')
    (he : R * e + Y * (e + L) + (u * u * (R * H) + 2 * η) + (u * (R * L + Mb) + η) +
      u * (Ttl + W1) + (u * (Y * H + T1) + η) + u * (u * (Ma + Th) + W2) ≤ e')
    (hov : Ma + Th + R * H + R * L + Mb + Ttl + W1 + T1 + Y * H + W2 ≤ 2 ^ 1000) :
    Pr (Erfc.fastTwoSum a (Erfc.aMul w h).1).1
      ((Erfc.fastTwoSum a (Erfc.aMul w h).1).2 +
        Library.Numerics.Arithmetic.Fma.fma y h ((Erfc.aMul w h).2 + Library.Numerics.Arithmetic.Fma.fma w l b))
      (fv a + fv b + (fv w + fv y) * V) M' L' e' := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hwR
  have hY0 : 0 ≤ Y := (abs_nonneg _).trans hyY
  have hL0 := hp.L_nonneg
  have hM0 := hp.M_nonneg
  have he0 := hp.e_nonneg
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans hMb
  have hMa0 : 0 ≤ Ma := (abs_nonneg _).trans hMa
  have hhH : |fv h| ≤ H := hp.h_le.trans hH
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hhH
  have hRH : 0 ≤ R * H := mul_nonneg hR0 hH0
  have hRL : 0 ≤ R * L := mul_nonneg hR0 hL0
  have hYH : 0 ≤ Y * H := mul_nonneg hY0 hH0
  have hu : (0 : ℝ) ≤ u := by positivity
  have hη : (0 : ℝ) ≤ η := by positivity
  obtain ⟨m1, m2, mth, mtl, msum⟩ := amul_bound hF hw hp.1 hwR hhH (by linarith)
  have hth : |fv (Erfc.aMul w h).1| ≤ Th := mth.trans hTh
  have htl : |fv (Erfc.aMul w h).2| ≤ Ttl := mtl.trans hTtl
  have hTh0 : 0 ≤ Th := (abs_nonneg _).trans hth
  have hTtl0 : 0 ≤ Ttl := (abs_nonneg _).trans htl
  obtain ⟨f1, f2, fsum, ft⟩ := fts_bound ha m1 hMa hth (hth.trans (hpre.trans hma))
    (by linarith)
  obtain ⟨w1, werr, wmag⟩ := fma_bound hF hw hp.2.1 hb hwR hp.2.2.2.2 hMb (by linarith)
  have hw1 : |fv (Library.Numerics.Arithmetic.Fma.fma w l b)| ≤ W1 := wmag.trans hW1
  have hW10 : 0 ≤ W1 := (abs_nonneg _).trans hw1
  obtain ⟨t1, terr, tmag⟩ := add_bound m2 w1 htl hw1 (by linarith)
  have ht1 : |fv ((Erfc.aMul w h).2 + Library.Numerics.Arithmetic.Fma.fma w l b)| ≤ T1 := tmag.trans hT1
  have hT10 : 0 ≤ T1 := (abs_nonneg _).trans ht1
  obtain ⟨w2, w2err, w2mag⟩ := fma_bound hF hy hp.1 t1 hyY hhH ht1 (by linarith)
  have hw2 : |fv (Library.Numerics.Arithmetic.Fma.fma y h ((Erfc.aMul w h).2 + Library.Numerics.Arithmetic.Fma.fma w l b))| ≤ W2 := w2mag.trans hW2
  have hW20 : 0 ≤ W2 := (abs_nonneg _).trans hw2
  have hut : u * (Ma + Th) ≤ Ma + Th := by
    have : u ≤ 1 := by norm_num
    nlinarith
  obtain ⟨s1, serr, smag⟩ := add_bound f2 w2 ft hw2 (by linarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · set th := fv (Erfc.aMul w h).1
    set tl := fv (Erfc.aMul w h).2
    set t := fv (Erfc.fastTwoSum a (Erfc.aMul w h).1).2
    set f := fv (Library.Numerics.Arithmetic.Fma.fma w l b)
    set tt := fv ((Erfc.aMul w h).2 + Library.Numerics.Arithmetic.Fma.fma w l b)
    set g := fv (Library.Numerics.Arithmetic.Fma.fma y h ((Erfc.aMul w h).2 + Library.Numerics.Arithmetic.Fma.fma w l b))
    set lo := fv ((Erfc.fastTwoSum a (Erfc.aMul w h).1).2 +
      Library.Numerics.Arithmetic.Fma.fma y h ((Erfc.aMul w h).2 + Library.Numerics.Arithmetic.Fma.fma w l b))
    have e1 : fv (Erfc.fastTwoSum a (Erfc.aMul w h).1).1 + lo -
        (fv a + fv b + (fv w + fv y) * V) =
        (th + tl - fv w * fv h) + (f - (fv w * fv l + fv b)) + (tt - (tl + f)) +
          (g - (fv y * fv h + tt)) + (lo - (t + g)) + fv w * (fv h + fv l - V) +
          fv y * (fv h - V) := by
      linear_combination fsum
    rw [e1]
    have hz1 : |fv w * (fv h + fv l - V)| ≤ R * e := by
      rw [abs_mul]; exact mul_le_mul hwR hp.2.2.1 (abs_nonneg _) hR0
    have hhV : |fv h - V| ≤ e + L := by
      have : fv h - V = (fv h + fv l - V) - fv l := by ring
      rw [this]
      exact (abs_sub_le' _ _).trans (by linarith [hp.2.2.1, hp.2.2.2.2])
    have hz2 : |fv y * (fv h - V)| ≤ Y * (e + L) := by
      rw [abs_mul]; exact mul_le_mul hyY hhV (abs_nonneg _) hY0
    have k1 := abs_add3 (th + tl - fv w * fv h) (f - (fv w * fv l + fv b)) (tt - (tl + f))
    have k2 := abs_add3 (th + tl - fv w * fv h + (f - (fv w * fv l + fv b)) + (tt - (tl + f)))
      (g - (fv y * fv h + tt)) (lo - (t + g))
    have k3 := abs_add3 (th + tl - fv w * fv h + (f - (fv w * fv l + fv b)) + (tt - (tl + f)) +
      (g - (fv y * fv h + tt)) + (lo - (t + g))) (fv w * (fv h + fv l - V)) (fv y * (fv h - V))
    linarith
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul (show |fv w + fv y| ≤ R + Y from (abs_add_le _ _).trans (by linarith))
      hp.2.2.2.1 (abs_nonneg _) (by linarith)
    have := abs_add_le (fv a) (fv b)
    linarith

/-- `(h, l) z`: `aMul h z` with `l z` added to its error term by one `fma`. -/
theorem pr_mulG (hF : FmaNearest) {z h l : Float} {V M L e R : ℝ} (hz : ff z) (hzR : |fv z| ≤ R)
    (hp : Pr h l V M L e) (H Ttl M' L' e' : ℝ) (hH : M + e + L ≤ H)
    (hTtl : u * u * (H * R) + 2 * η + (u * (H * R) + η) ≤ Ttl)
    (hM : M * R ≤ M') (hL : (L * R + Ttl) * (1 + u) + η ≤ L')
    (he : R * e + (u * u * (H * R) + 2 * η) + (u * (L * R + Ttl) + η) ≤ e')
    (hov : H * R + L * R + Ttl ≤ 2 ^ 1000) :
    Pr (Erfc.aMul h z).1 (Library.Numerics.Arithmetic.Fma.fma l z (Erfc.aMul h z).2) (V * fv z) M' L' e' := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hzR
  have hL0 := hp.L_nonneg
  have he0 := hp.e_nonneg
  have hhH : |fv h| ≤ H := hp.h_le.trans hH
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hhH
  have hu : (0 : ℝ) ≤ u := by positivity
  have hη : (0 : ℝ) ≤ η := by positivity
  have hHR : 0 ≤ H * R := mul_nonneg hH0 hR0
  have hLR : 0 ≤ L * R := mul_nonneg hL0 hR0
  obtain ⟨m1, m2, mth, mtl, msum⟩ := amul_bound hF hp.1 hz hhH hzR (by linarith)
  have htl : |fv (Erfc.aMul h z).2| ≤ Ttl := mtl.trans hTtl
  have hTtl0 : 0 ≤ Ttl := (abs_nonneg _).trans htl
  obtain ⟨w1, werr, wmag⟩ := fma_bound hF hp.2.1 hz m2 hp.2.2.2.2 hzR htl (by linarith)
  refine ⟨m1, w1, ?_, ?_, wmag.trans hL⟩
  · have e1 : fv (Erfc.aMul h z).1 + fv (Library.Numerics.Arithmetic.Fma.fma l z (Erfc.aMul h z).2) - V * fv z =
        (fv (Erfc.aMul h z).1 + fv (Erfc.aMul h z).2 - fv h * fv z) +
          (fv (Library.Numerics.Arithmetic.Fma.fma l z (Erfc.aMul h z).2) - (fv l * fv z + fv (Erfc.aMul h z).2)) +
          fv z * (fv h + fv l - V) := by ring
    rw [e1]
    have hz1 : |fv z * (fv h + fv l - V)| ≤ R * e := by
      rw [abs_mul]; exact mul_le_mul hzR hp.2.2.1 (abs_nonneg _) hR0
    have k1 := abs_add3 (fv (Erfc.aMul h z).1 + fv (Erfc.aMul h z).2 - fv h * fv z)
      (fv (Library.Numerics.Arithmetic.Fma.fma l z (Erfc.aMul h z).2) - (fv l * fv z + fv (Erfc.aMul h z).2))
      (fv z * (fv h + fv l - V))
    linarith
  · rw [abs_mul]
    exact (mul_le_mul hp.2.2.2.1 hzR (abs_nonneg _) hp.M_nonneg).trans hM

/-- A double-double within `e` of `V` lies within `e + d` of any `V'` with `|V - V'| ≤ d`. -/
theorem _root_.Library.Numerics.Float64.Erfc.ErfcTrack.Pr.shift {h l : Float} {V M L e : ℝ} (hp : Pr h l V M L e) (V' d : ℝ)
    (hd : |V - V'| ≤ d) (M' e' : ℝ) (hM : M + d ≤ M') (he : e + d ≤ e') :
    Pr h l V' M' L e' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  refine ⟨h1, h2, ?_, ?_, h5⟩
  · have : fv h + fv l - V' = (fv h + fv l - V) + (V - V') := by ring
    rw [this]; exact (abs_add_le _ _).trans (by linarith)
  · have : V' = V - (V - V') := by ring
    rw [this]; exact (abs_sub_le' _ _).trans (by linarith)

/-- `Pr.shift` for a change of one factor of the target. -/
theorem _root_.Library.Numerics.Float64.Erfc.ErfcTrack.Pr.shift_mul {h l : Float} {A w v M L e : ℝ} (hp : Pr h l (A + w * v) M L e)
    (w' ew Mv d : ℝ) (hw : |w - w'| ≤ ew) (hv : |v| ≤ Mv) (hd : ew * Mv ≤ d) (M' e' : ℝ)
    (hM : M + d ≤ M') (he : e + d ≤ e') : Pr h l (A + w' * v) M' L e' := by
  refine hp.shift _ d ?_ M' e' hM he
  rw [show A + w * v - (A + w' * v) = (w - w') * v by ring, abs_mul]
  exact (mul_le_mul hw hv (abs_nonneg _) ((abs_nonneg _).trans hw)).trans hd

#print axioms pr_mulE
#print axioms pr_mulF
#print axioms pr_mulG

end Library.Numerics.Float64.Erfc.ErfcTrack2
