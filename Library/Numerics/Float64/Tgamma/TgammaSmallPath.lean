import Library.Numerics.Float64.Tgamma.TgammaSmall
import Library.Numerics.Float64.Tgamma.TgammaRecip
import Library.Numerics.Float64.Tgamma.TgammaBranches
import LeanExe.ProofKit.GammaBasic

/-!
**The fast path of `tgammaWith` from `2 ^ -112` to `1/4`** within one step of `Γ`.  With
`R = 1/|x|`, the corrected reciprocal (`TgammaRecip.recip_corr`), the polynomial
(`TgammaSmall.small_poly`), and their `fastSum` give `1/x + smallPoly x` within `2 ^ -56 R`
(`small_sum`).  `SmallFact` puts `Γ x` within `2 ^ -60 R` of it, and `GammaBasic.gamma_sub_inv_bounds`
gives `0.6 R ≤ |Γ x|`.  The test term `eps` stays below `2 ^ -58 R`, so the rounded sum
`fh + (fl + eps)` lies within `2 ^ -55` of `Γ x` relative, and `within_one_of_rounded_rel` gives one
step (`smallPath_within`).  The rounding test of the code is not used: when it fails, the result
is that of the accurate path, which the theorem takes as a hypothesis.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaSmallPath
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPoly TgammaPolyDDD
  TgammaExpr TgammaWords TgammaSmall TgammaRecip

set_option exponentiation.threshold 4096

/-- The factor `3.5e-19 + x^6 4e-15` of `eps`. -/
def epsE : FE := .add (.const 0x3C19D35025BFF857) (.mul (.mul x2E x4E) (.const 0x3CF203AF9EE75616))

theorem epsE_ok : ok epsE (1 / 4) = true := by decide +kernel

theorem epsE_bnd : (bnd epsE (1 / 4)).1 + (bnd epsE (1 / 4)).2 ≤ 1 / 2 ^ 59 := by decide +kernel

/-- The sum of the corrected reciprocal and the polynomial. -/
theorem small_sum (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (x : Float) (hx : Finite x.toBits)
    (h1 : 1 / 2 ^ 112 ≤ |value x.toBits|) (h2 : |value x.toBits| ≤ 1 / 4) :
    let p := polyDDD smallTable 0 5 x (evalF lE x)
    let q := fastSum (1.0 / x) (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / x) (-x) 1.0 * (1.0 / x)) p.1 p.2
    Finite q.1.toBits ∧ Finite q.2.toBits ∧
      |value q.1.toBits + value q.2.toBits -
          (1 / value x.toBits + TgammaApprox.smallPoly (value x.toBits))| ≤
        |1 / value x.toBits| / 2 ^ 56 ∧
      |value q.1.toBits| ≤ 2 * |1 / value x.toBits| ∧
      |value q.2.toBits| ≤ |1 / value x.toBits| / 2 ^ 43 := by
  intro p q
  set vx := value x.toBits with hvx
  set R := |1 / vx| with hR
  have hx0 : 0 < |vx| := lt_of_lt_of_le (by positivity) h1
  have hRv : R = 1 / |vx| := by rw [hR, abs_div, abs_one]
  have hR4 : 4 ≤ R := by rw [hRv, le_div_iff₀ hx0]; linarith
  obtain ⟨hff, hcf, hfe, hcb, hfc⟩ := recip_corr hF x hx (le_trans (by norm_num) h1) h2
  obtain ⟨hp1, hp2, hpe, hpl⟩ := small_poly hF x hx h2
  -- the polynomial is below 1
  have hS : |TgammaApprox.smallPoly vx| ≤ 23 / 25 := by
    rw [← horner_small vx]
    refine (horner_bound_pow _ 5 _ vx (1 / 4) h2 4 (by norm_num)).trans ?_
    have hL : |evalR lE vx| ≤ 1 / 2 := by
      have := (evalF_approx lE (1 / 4) x hx (by push_cast; exact h2) lE_ok).2
      have h' : ((bnd lE (1 / 4)).1 : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast lE_mag
      push_cast at h'
      linarith
    have hc : ∀ k ∈ Finset.range (4 + 1),
        |cDD smallTable 0 (5 - 1 - 4 + k)| * (1 / 4 : ℝ) ^ k =
          ((PolyBound.qabs (PolyBound.ratOfWord smallTable[2 * k]! +
            PolyBound.ratOfWord smallTable[2 * k + 1]!) * (1 / 4) ^ k : ℚ) : ℝ) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show 5 - 1 - 4 + k = k by omega,
        cDD_rat smallTable 0 k (w_finite _ (by simp; omega)) (w_finite _ (by simp; omega))]
      push_cast
      rw [qabs_cast]
      simp
    rw [Finset.sum_congr rfl hc, ← Rat.cast_sum]
    have hsum : (∑ k ∈ Finset.range (4 + 1), PolyBound.qabs (PolyBound.ratOfWord smallTable[2 * k]! +
        PolyBound.ratOfWord smallTable[2 * k + 1]!) * (1 / 4) ^ k : ℚ) ≤ 91 / 100 := by
      decide +kernel
    have hs' : ((∑ k ∈ Finset.range (4 + 1), PolyBound.qabs (PolyBound.ratOfWord smallTable[2 * k]! +
        PolyBound.ratOfWord smallTable[2 * k + 1]!) * (1 / 4) ^ k : ℚ) : ℝ) ≤ 91 / 100 := by
      calc _ ≤ ((91 / 100 : ℚ) : ℝ) := Rat.cast_le.mpr hsum
        _ = 91 / 100 := by norm_num
    have : |evalR lE vx| * (1 / 4) ^ 4 ≤ 1 / 2 * (1 / 4) ^ 4 :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    linarith
  set p1 := p.1
  set p2 := p.2
  have hp1b : |value p1.toBits| ≤ 1 := by
    have := abs_sub_abs_le_abs_sub (value p1.toBits + value p2.toBits) (TgammaApprox.smallPoly vx)
    have h3 := abs_add_le (value p1.toBits) (value p2.toBits)
    have h4 := abs_sub_abs_le_abs_sub (value p1.toBits) (-(value p2.toBits))
    rw [sub_neg_eq_add, abs_neg] at h4
    linarith [(by norm_num : (23 : ℝ) / 25 + 1 / 2 ^ 55 + 2 * (1 / 2 ^ 43) ≤ 1)]
  set fh := (1.0 : Float) / x
  set cr := Library.Numerics.Arithmetic.Fma.Fma.fma fh (-x) 1.0 * fh
  have hfhb : R / 2 ≤ |value fh.toBits| := by
    have := abs_sub_abs_le_abs_sub (1 / vx) (value fh.toBits)
    rw [abs_sub_comm] at this
    have : R / 2 ^ 52 ≤ R / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) (by norm_num)
    linarith
  have hfhb2 : |value fh.toBits| ≤ 2 * R := by
    have := abs_sub_abs_le_abs_sub (value fh.toBits) (1 / vx)
    have : R / 2 ^ 52 ≤ R := div_le_self (by linarith) (by norm_num)
    linarith
  have hRmax : R ≤ 2 ^ 112 := by
    rw [hRv, div_le_iff₀ hx0]
    calc (1 : ℝ) = 2 ^ 112 * (1 / 2 ^ 112) := by norm_num
      _ ≤ 2 ^ 112 * |vx| := by gcongr
  have hord : |value p1.toBits| ≤ |value fh.toBits| := by linarith
  have hlim : |value fh.toBits| < 2 ^ 898 := by
    linarith [(by norm_num : (2 : ℝ) * 2 ^ 112 < 2 ^ 898)]
  set L := R / 2 ^ 50 + 1 / 2 ^ 43 with hLdef
  have hLb : |value cr.toBits| + |value p2.toBits| ≤ L := by rw [hLdef]; linarith
  have hLmax : L ≤ 2 ^ 800 := by
    rw [hLdef]
    have : R / 2 ^ 50 ≤ R := div_le_self (by linarith) (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 112 + 1 / 2 ^ 43 ≤ 2 ^ 800)]
  obtain ⟨hq1, hq2, hqe, hqb⟩ := fastSum_spec fh cr p1 p2 hff hcf hp1 hp2 hord hlim L hLb hLmax
  have hL49 : L ≤ R / 2 ^ 44 := by
    rw [hLdef]
    have : (1 : ℝ) / 2 ^ 43 ≤ R / 2 ^ 45 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hR0 : 0 ≤ R := by linarith
  have htiny : (1 : ℝ) / 2 ^ 1073 ≤ R / 2 ^ 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hq1b : |value q.1.toBits| ≤ 2 * R := by
    have h3 := abs_sub_abs_le_abs_sub (value q.1.toBits + value q.2.toBits)
      (value fh.toBits + value cr.toBits + (value p1.toBits + value p2.toBits))
    have h4 := abs_sub_abs_le_abs_sub (value q.1.toBits) (-(value q.2.toBits))
    rw [sub_neg_eq_add, abs_neg] at h4
    have h5 := abs_add_le (value fh.toBits + value cr.toBits) (value p1.toBits + value p2.toBits)
    have h6 := abs_sub_abs_le_abs_sub (value fh.toBits + value cr.toBits) (1 / vx)
    have h8 := abs_sub_abs_le_abs_sub (value p1.toBits + value p2.toBits)
      (TgammaApprox.smallPoly vx)
    have h9 : R / 2 ^ 100 ≤ R := div_le_self hR0 (by norm_num)
    linarith
  refine ⟨hq1, hq2, ?_, hq1b, ?_⟩
  · have hsplit : value q.1.toBits + value q.2.toBits - (1 / vx + TgammaApprox.smallPoly vx) =
        (value q.1.toBits + value q.2.toBits -
          (value fh.toBits + value cr.toBits + (value p1.toBits + value p2.toBits))) +
        (value fh.toBits + value cr.toBits - 1 / vx) +
        (value p1.toBits + value p2.toBits - TgammaApprox.smallPoly vx) := by ring
    rw [hsplit]
    have h3 := abs_add_le (value q.1.toBits + value q.2.toBits -
          (value fh.toBits + value cr.toBits + (value p1.toBits + value p2.toBits)) +
        (value fh.toBits + value cr.toBits - 1 / vx))
      (value p1.toBits + value p2.toBits - TgammaApprox.smallPoly vx)
    have h4 := abs_add_le (value q.1.toBits + value q.2.toBits -
          (value fh.toBits + value cr.toBits + (value p1.toBits + value p2.toBits)))
        (value fh.toBits + value cr.toBits - 1 / vx)
    have h55 : (1 : ℝ) / 2 ^ 55 ≤ R / 2 ^ 57 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h1074 : (1 : ℝ) / 2 ^ 1074 ≤ R / 2 ^ 1000 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have hq : (3 * L + |value q.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ≤ R / 2 ^ 95 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  · linarith

/-- `Γ` below `1/4` against `1/x + smallPoly x`, and its size. -/
theorem small_gamma (hS : TgammaApprox.SmallFact) (x : ℝ) (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 4) :
    |Real.Gamma x - (1 / x + TgammaApprox.smallPoly x)| ≤ |1 / x| / 2 ^ 60 ∧
      3 / 5 * |1 / x| ≤ |Real.Gamma x| ∧ |Real.Gamma x| ≤ 7 / 5 * |1 / x| := by
  have hx0' : 0 < |x| := abs_pos.mpr hx0
  have hR : |1 / x| = 1 / |x| := by rw [abs_div, abs_one]
  have hR4 : 4 ≤ |1 / x| := by rw [hR, le_div_iff₀ hx0']; linarith
  refine ⟨?_, ?_⟩
  · have h := hS x hx
    rw [add_comm, Real.Gamma_add_one hx0] at h
    have hid : Real.Gamma x - (1 / x + TgammaApprox.smallPoly x) =
        (x * Real.Gamma x - (1 + x * TgammaApprox.smallPoly x)) / x := by
      field_simp
    rw [hid, abs_div, hR, div_div, div_le_div_iff₀ hx0' (by positivity)]
    calc |x * Real.Gamma x - (1 + x * TgammaApprox.smallPoly x)| * (|x| * 2 ^ 60)
        ≤ 1 / 2 ^ 60 * (|x| * 2 ^ 60) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = 1 * |x| := by field_simp
  · obtain ⟨hlo, hhi⟩ := GammaBasic.gamma_sub_inv_bounds hx0 (by linarith [neg_abs_le x])
      (by linarith [le_abs_self x])
    have h1 := abs_sub_abs_le_abs_sub (1 / x) (Real.Gamma x)
    have h2 := abs_sub_abs_le_abs_sub (Real.Gamma x) (1 / x)
    have h3 : |Real.Gamma x - 1 / x| ≤ 8 / 5 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_sub_comm] at h1
    constructor <;> linarith

theorem smallPath_eq (dbTab accTab : Array UInt64) (x : Float) :
    TgammaBranches.smallPath dbTab accTab smallTable x =
      (let p := polyDDD smallTable 0 5 x (evalF lE x)
       let q := fastSum (1.0 / x) (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / x) (-x) 1.0 * (1.0 / x)) p.1 p.2
       let eps := q.1 * evalF epsE x
       if (q.1 + (q.2 + eps)) != (q.1 + (q.2 - eps)) then accurate accTab dbTab x
       else q.1 + (q.2 + eps)) := rfl

/-- **The fast path below `1/4`** within one step of `Γ`, when the accurate path is. -/
theorem smallPath_within (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hS : TgammaApprox.SmallFact)
    (dbTab accTab : Array UInt64) (x : Float) (hx : Finite x.toBits)
    (h1 : 1 / 2 ^ 112 ≤ |value x.toBits|) (h2 : |value x.toBits| ≤ 1 / 4)
    (hacc : F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (accurate accTab dbTab x).toBits) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (TgammaBranches.smallPath dbTab accTab smallTable x).toBits := by
  rw [smallPath_eq]
  set vx := value x.toBits with hvx
  have hx0' : 0 < |vx| := lt_of_lt_of_le (by positivity) h1
  have hx0 : vx ≠ 0 := abs_pos.mp hx0'
  set R := |1 / vx| with hR
  have hRv : R = 1 / |vx| := by rw [hR, abs_div, abs_one]
  have hR4 : 4 ≤ R := by rw [hRv, le_div_iff₀ hx0']; linarith
  have hRmax : R ≤ 2 ^ 112 := by
    rw [hRv, div_le_iff₀ hx0']
    calc (1 : ℝ) = 2 ^ 112 * (1 / 2 ^ 112) := by norm_num
      _ ≤ 2 ^ 112 * |vx| := by gcongr
  obtain ⟨hgS, hglo, hghi⟩ := small_gamma hS vx hx0 h2
  set G := Real.Gamma vx with hG
  obtain ⟨hq1f, hq2f, hqe, hq1b, hq2b⟩ := small_sum hF x hx h1 h2
  set p := polyDDD smallTable 0 5 x (evalF lE x)
  set q := fastSum (1.0 / x) (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / x) (-x) 1.0 * (1.0 / x)) p.1 p.2
  -- `eps`
  obtain ⟨hf, hfm⟩ := evalF_approx epsE (1 / 4) x hx (by push_cast; exact h2) epsE_ok
  have hfb : |value (evalF epsE x).toBits| ≤ 1 / 2 ^ 59 := by
    have h := abs_sub_abs_le_abs_sub (value (evalF epsE x).toBits) (evalR epsE vx)
    have h' : (((bnd epsE (1 / 4)).1 + (bnd epsE (1 / 4)).2 : ℚ) : ℝ) ≤ ((1 / 2 ^ 59 : ℚ) : ℝ) := by
      exact_mod_cast epsE_bnd
    push_cast at h'
    linarith [hf.2]
  have hR0 : 0 ≤ R := by linarith
  have hem := fapprox_mul (fapprox_self q.1 hq1f) (fapprox_self _ hf.1) |value q.1.toBits|
    (1 / 2 ^ 59) le_rfl hfb (2 * R * (1 / 2 ^ 59)) (by
      simp only [add_zero]; exact mul_le_mul hq1b le_rfl (by positivity) (by positivity))
    (by nlinarith [(by norm_num : (2 : ℝ) * 2 ^ 112 * (1 / 2 ^ 59) < 2 ^ 1022)])
  set e := q.1 * evalF epsE x
  have heb : |value e.toBits| ≤ R / 2 ^ 57 := by
    have h := hem.2
    simp only [zero_mul, mul_zero, add_zero, zero_add] at h
    have h3 := abs_sub_abs_le_abs_sub (value e.toBits) (value q.1.toBits * value (evalF epsE x).toBits)
    have h4 : |value q.1.toBits * value (evalF epsE x).toBits| ≤ 2 * R * (1 / 2 ^ 59) := by
      rw [abs_mul]; exact mul_le_mul hq1b hfb (abs_nonneg _) (by positivity)
    have htiny : (1 : ℝ) / 2 ^ 1075 ≤ R / 2 ^ 1000 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  -- `a = q.2 + eps`
  have ha := fapprox_add (fapprox_self q.2 hq2f) (fapprox_self e hem.1) (R / 2 ^ 43 + R / 2 ^ 57)
    (by simp only [add_zero]; linarith [abs_add_le (value q.2.toBits) (value e.toBits)])
    (by linarith [(by norm_num : (2 : ℝ) ^ 112 / 2 ^ 43 + 2 ^ 112 / 2 ^ 57 < 2 ^ 1023),
      div_le_div_of_nonneg_right hRmax (by norm_num : (0 : ℝ) ≤ 2 ^ 43),
      div_le_div_of_nonneg_right hRmax (by norm_num : (0 : ℝ) ≤ 2 ^ 57)])
  set a := q.2 + e
  have hae : |value a.toBits - (value q.2.toBits + value e.toBits)| ≤ R / 2 ^ 95 := by
    have h := ha.2
    simp only [zero_add] at h
    have : (R / 2 ^ 43 + R / 2 ^ 57) / 2 ^ 53 ≤ R / 2 ^ 95 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  -- the exact sum before the last rounding
  set S' := value q.1.toBits + value a.toBits with hS'
  have hS'G : |S' - G| ≤ |G| / 2 ^ 54 := by
    have hsplit : S' - G = (value q.1.toBits + value q.2.toBits - (1 / vx + TgammaApprox.smallPoly vx)) +
        (1 / vx + TgammaApprox.smallPoly vx - G) + value e.toBits +
        (value a.toBits - (value q.2.toBits + value e.toBits)) := by rw [hS']; ring
    rw [hsplit]
    have h3 := abs_add_le (value q.1.toBits + value q.2.toBits - (1 / vx + TgammaApprox.smallPoly vx) +
        (1 / vx + TgammaApprox.smallPoly vx - G) + value e.toBits)
      (value a.toBits - (value q.2.toBits + value e.toBits))
    have h4 := abs_add_le (value q.1.toBits + value q.2.toBits - (1 / vx + TgammaApprox.smallPoly vx) +
        (1 / vx + TgammaApprox.smallPoly vx - G)) (value e.toBits)
    have h5 := abs_add_le (value q.1.toBits + value q.2.toBits - (1 / vx + TgammaApprox.smallPoly vx))
        (1 / vx + TgammaApprox.smallPoly vx - G)
    rw [abs_sub_comm] at hgS
    have : R / 2 ^ 56 + R / 2 ^ 60 + R / 2 ^ 57 + R / 2 ^ 95 ≤ 3 / 5 * R / 2 ^ 54 := by
      rw [show 3 / 5 * R / 2 ^ 54 = R * (3 / 5 / 2 ^ 54) by ring]
      have : R / 2 ^ 56 + R / 2 ^ 60 + R / 2 ^ 57 + R / 2 ^ 95 = R * (1 / 2 ^ 56 + 1 / 2 ^ 60 +
          1 / 2 ^ 57 + 1 / 2 ^ 95) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by norm_num) hR0
    have : 3 / 5 * R / 2 ^ 54 ≤ |G| / 2 ^ 54 := div_le_div_of_nonneg_right hglo (by positivity)
    linarith
  have hG0 : 0 < |G| := lt_of_lt_of_le (by positivity) hglo
  have hS'0 : S' ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hS'G
    have : |G| / 2 ^ 54 < |G| := div_lt_self hG0 (by norm_num)
    linarith
  have hS'max : |S'| < 2 ^ 1023 := by
    have := abs_sub_abs_le_abs_sub S' G
    have : |G| / 2 ^ 54 ≤ |G| := div_le_self hG0.le (by norm_num)
    nlinarith [(by norm_num : (7 : ℝ) / 5 * 2 ^ 112 * 2 < 2 ^ 1023)]
  have hround := F64RoundNearest.add_rounded q.1.toBits a.toBits hq1f ha.1 hS'0 hS'max
  rw [← F64Bits.toBits_add] at hround
  have hwithin : F64SignedRounding.WithinSteps 1 G (q.1 + a).toBits :=
    F64RoundNearest.within_one_of_rounded_rel _ S' G hround (1 / 2 ^ 54) (by positivity)
      (by norm_num) (by rw [one_div_mul_eq_div]; exact hS'G)
      (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1021 ≤ 3 / 5 * 4)])
      (by nlinarith [(by norm_num : (7 : ℝ) / 5 * 2 ^ 112 < 2 ^ 1022)])
  simp only []
  by_cases hc : (q.1 + (q.2 + e) != q.1 + (q.2 - e)) = true
  · rw [ite_eq_left hc]
    exact hacc
  · rw [ite_eq_right hc]
    exact hwithin

#print axioms small_sum
#print axioms small_gamma
#print axioms smallPath_within

end Library.Numerics.Float64.Tgamma.TgammaSmallPath
