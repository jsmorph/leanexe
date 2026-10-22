import Library.Numerics.Float64.Tgamma.TgammaMulDD3
import Library.Numerics.Float64.Tgamma.TgammaRecipDD

/-!
The combination of the polynomial `fh + fl` with the product `wh + wl` of the shift loop in
`Tgamma.accurate`: the quotient by the corrected reciprocal for `x < j` (`div_step`) and the
product for `x ≥ j + 1` (`mul_step`), each within `2 ^ -76` relative.  Both use
`TgammaMulDD3.mulDD3_wide`, since the low part of the polynomial is only known below `2 ^ -30` of
its high part.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAccComb
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD

set_option exponentiation.threshold 4096

/-- **The quotient** `(fh + fl) / (wh + wl)` with `rh = 1/wh` and its correction. -/
theorem div_step (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (fh fl wh wl : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (hwh : Finite wh.toBits) (hwl : Finite wl.toBits)
    (hflb : |value fl.toBits| ≤ |value fh.toBits| / 2 ^ 30) (hfh1 : 1 / 32 ≤ |value fh.toBits|)
    (hfh2 : |value fh.toBits| ≤ 2 ^ 8) (hwlb : |value wl.toBits| ≤ |value wh.toBits| / 2 ^ 50)
    (hwh1 : 1 / 2 ^ 60 ≤ |value wh.toBits|) (hwh2 : |value wh.toBits| ≤ 2 ^ 519) :
    Finite (mulDD3 fh fl (1.0 / wh)
        ((Library.Numerics.Arithmetic.Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh))).1.toBits ∧
      Finite (mulDD3 fh fl (1.0 / wh)
        ((Library.Numerics.Arithmetic.Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh))).2.toBits ∧
      |value (mulDD3 fh fl (1.0 / wh)
          ((Library.Numerics.Arithmetic.Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh))).1.toBits +
        value (mulDD3 fh fl (1.0 / wh)
          ((Library.Numerics.Arithmetic.Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh))).2.toBits -
        (value fh.toBits + value fl.toBits) / (value wh.toBits + value wl.toBits)| ≤
        |(value fh.toBits + value fl.toBits) / (value wh.toBits + value wl.toBits)| / 2 ^ 76 ∧
      |value (mulDD3 fh fl (1.0 / wh)
          ((Library.Numerics.Arithmetic.Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh))).2.toBits| ≤
        |value (mulDD3 fh fl (1.0 / wh)
          ((Library.Numerics.Arithmetic.Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh))).1.toBits| / 2 ^ 51 := by
  obtain ⟨hrf, hcf, hre, hcb, hrb⟩ := TgammaRecipDD.recip_dd hF wh wl hwh hwl
    (hwlb.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num)))
    (le_trans (by norm_num) hwh1) (hwh2.trans (by norm_num))
  set a := value fh.toBits
  set b := value fl.toBits
  set c := value wh.toBits
  set e := value wl.toBits
  have hc0 : 0 < |c| := lt_of_lt_of_le (by positivity) hwh1
  -- `D = wh + wl`
  have hD1 : |c| * (1 - 1 / 2 ^ 50) ≤ |c + e| := by
    have := abs_sub_abs_le_abs_sub c (-e)
    rw [sub_neg_eq_add, abs_neg] at this
    nlinarith
  have hD2 : |c + e| ≤ |c| * (1 + 1 / 2 ^ 50) := by
    have := abs_add_le c e
    nlinarith
  have hDp : 0 < |c + e| := lt_of_lt_of_le (by nlinarith) hD1
  set r := (1.0 : Float) / wh with hrdef
  set k := (Library.Numerics.Arithmetic.Fma.fma r (-wh) 1.0 - wl * r) * r with hkdef
  set R := |1 / (c + e)| with hR
  have hRv : R = 1 / |c + e| := by rw [hR, abs_div, abs_one]
  have hr1 : R * (1 - 1 / 2 ^ 38) ≤ |value r.toBits| := by
    have h1 := abs_sub_abs_le_abs_sub (1 / (c + e)) (value r.toBits + value k.toBits)
    rw [abs_sub_comm] at h1
    have h2 := abs_add_le (value r.toBits) (value k.toBits)
    have h3 : R / 2 ^ 78 + |value r.toBits| / 2 ^ 38 ≤
        R / 2 ^ 78 + R * (1 + 1 / 2 ^ 38) / 2 ^ 38 := by
      gcongr
    nlinarith [abs_nonneg (value r.toBits)]
  -- the product by `mulDD3`
  have hab1 : |a| * (|value r.toBits|) ≤ 2 ^ 8 * (R * (1 + 1 / 2 ^ 38)) :=
    mul_le_mul hfh2 hrb (abs_nonneg _) (by positivity)
  have hRb : R ≤ 2 ^ 61 := by
    rw [hRv, div_le_iff₀ hDp]
    nlinarith [(by norm_num : (1 : ℝ) ≤ 2 ^ 61 * (1 / 2 ^ 60 * (1 - 1 / 2 ^ 50)))]
  have hRl : 1 / 2 ^ 520 ≤ R := by
    rw [hRv, le_div_iff₀ hDp]
    nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 520 * (2 ^ 519 * (1 + 1 / 2 ^ 50)) ≤ 1)]
  obtain ⟨hpf, hp2f, hpe, hp2b, -, -⟩ := TgammaMulDD3.mulDD3_wide hF fh fl r k hfh hfl hrf hcf hflb
    (hcb.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num)))
    (by
      have : 1 / 32 * (R * (1 - 1 / 2 ^ 38)) ≤ |a| * |value r.toBits| :=
        mul_le_mul hfh1 hr1 (by positivity) (abs_nonneg _)
      nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 900 ≤ 1 / 32 * (1 / 2 ^ 520 * (1 - 1 / 2 ^ 38)))])
    (by nlinarith [(by norm_num : (2 : ℝ) ^ 8 * (2 ^ 61 * (1 + 1 / 2 ^ 38)) ≤ 2 ^ 899)])
  refine ⟨hpf, hp2f, ?_, hp2b⟩
  -- the error against the quotient
  have hq : (a + b) / (c + e) = (a + b) * (1 / (c + e)) := by ring
  have habl : |a| * (1 - 1 / 2 ^ 29) ≤ |a + b| := by
    have := abs_sub_abs_le_abs_sub a (-b)
    rw [sub_neg_eq_add, abs_neg] at this
    nlinarith
  set M := mulDD3 fh fl r k with hMdef
  have e1 : value M.1.toBits + value M.2.toBits - (a + b) / (c + e) =
      (value M.1.toBits + value M.2.toBits - (a + b) * (value r.toBits + value k.toBits)) +
        (a + b) * (value r.toBits + value k.toBits - 1 / (c + e)) := by rw [hq]; ring
  rw [e1, abs_div, show |a + b| / |c + e| = |a + b| * R by rw [hRv]; ring]
  have h2 := abs_add_le (value M.1.toBits + value M.2.toBits - (a + b) * (value r.toBits +
    value k.toBits)) ((a + b) * (value r.toBits + value k.toBits - 1 / (c + e)))
  have h3 : |(a + b) * (value r.toBits + value k.toBits - 1 / (c + e))| ≤
      |a + b| * (R / 2 ^ 78) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hre (abs_nonneg _)
  have h4 : |a| * |value r.toBits| / 2 ^ 78 ≤ |a + b| * R * (2 / 2 ^ 78) := by
    have : |a| * |value r.toBits| ≤ (|a + b| / (1 - 1 / 2 ^ 29)) * (R * (1 + 1 / 2 ^ 38)) := by
      apply mul_le_mul _ hrb (abs_nonneg _) (by positivity)
      rw [le_div_iff₀ (by norm_num)]; linarith
    have h5 : (|a + b| / (1 - 1 / 2 ^ 29)) * (R * (1 + 1 / 2 ^ 38)) ≤ |a + b| * R * 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
      have : 0 ≤ |a + b| * R := by positivity
      nlinarith
    have := div_le_div_of_nonneg_right (this.trans h5) (by positivity : (0 : ℝ) ≤ 2 ^ 78)
    linarith [(by ring : |a + b| * R * 2 / 2 ^ 78 = |a + b| * R * (2 / 2 ^ 78))]
  have : 0 ≤ |a + b| * R := by positivity
  nlinarith [(by norm_num : (2 : ℝ) / 2 ^ 78 + 1 / 2 ^ 78 ≤ 1 / 2 ^ 76)]

/-- **The product** `(fh + fl) (wh + wl)`. -/
theorem mul_step (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (fh fl wh wl : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (hwh : Finite wh.toBits) (hwl : Finite wl.toBits)
    (hflb : |value fl.toBits| ≤ |value fh.toBits| / 2 ^ 30) (hfh1 : 1 / 32 ≤ |value fh.toBits|)
    (hfh2 : |value fh.toBits| ≤ 2 ^ 8) (hwlb : |value wl.toBits| ≤ |value wh.toBits| / 2 ^ 50)
    (hwh1 : 1 ≤ |value wh.toBits|) (hwh2 : |value wh.toBits| ≤ 2 ^ 519) :
    Finite (mulDD3 fh fl wh wl).1.toBits ∧ Finite (mulDD3 fh fl wh wl).2.toBits ∧
      |value (mulDD3 fh fl wh wl).1.toBits + value (mulDD3 fh fl wh wl).2.toBits -
        (value fh.toBits + value fl.toBits) * (value wh.toBits + value wl.toBits)| ≤
        |(value fh.toBits + value fl.toBits) * (value wh.toBits + value wl.toBits)| / 2 ^ 76 ∧
      |value (mulDD3 fh fl wh wl).2.toBits| ≤ |value (mulDD3 fh fl wh wl).1.toBits| / 2 ^ 51 := by
  set a := value fh.toBits
  set b := value fl.toBits
  set c := value wh.toBits
  set e := value wl.toBits
  obtain ⟨hpf, hp2f, hpe, hp2b, -, -⟩ := TgammaMulDD3.mulDD3_wide hF fh fl wh wl hfh hfl hwh hwl
    hflb (hwlb.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num)))
    (by nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 900 ≤ 1 / 32)])
    (by nlinarith [(by norm_num : (2 : ℝ) ^ 8 * 2 ^ 519 ≤ 2 ^ 899)])
  refine ⟨hpf, hp2f, hpe.trans ?_, hp2b⟩
  have habl : |a| * (1 - 1 / 2 ^ 29) ≤ |a + b| := by
    have := abs_sub_abs_le_abs_sub a (-b)
    rw [sub_neg_eq_add, abs_neg] at this
    nlinarith
  have hcel : |c| * (1 - 1 / 2 ^ 49) ≤ |c + e| := by
    have := abs_sub_abs_le_abs_sub c (-e)
    rw [sub_neg_eq_add, abs_neg] at this
    nlinarith
  rw [abs_mul]
  have : |a| * |c| ≤ 2 * (|a + b| * |c + e|) := by
    have h1 : |a| * |c| * ((1 - 1 / 2 ^ 29) * (1 - 1 / 2 ^ 49)) ≤ |a + b| * |c + e| := by
      have := mul_le_mul habl hcel (by positivity) (abs_nonneg _)
      nlinarith
    nlinarith [abs_nonneg a, abs_nonneg c, mul_nonneg (abs_nonneg a) (abs_nonneg c)]
  have := div_le_div_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 2 ^ 78)
  have h0 : 0 ≤ |a + b| * |c + e| := by positivity
  linarith [(by ring : 2 * (|a + b| * |c + e|) / 2 ^ 78 = (|a + b| * |c + e|) / 2 ^ 77),
    div_le_div_of_nonneg_left h0 (by positivity : (0 : ℝ) < 2 ^ 76)
      (by norm_num : (2 : ℝ) ^ 76 ≤ 2 ^ 77)]

#print axioms div_step
#print axioms mul_step

end Library.Numerics.Float64.Tgamma.TgammaAccComb
