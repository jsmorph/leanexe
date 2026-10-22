import Library.Numerics.Float64.Erfc.ErfcAsymPoly
import Library.Numerics.Float64.Erfc.ErfcAsymPlan
import LeanExe.ProofKit.F64DivApprox
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
The polynomial of a row of `T` at the computed `U ≈ 1/x²`.  `asym_core_pr` bounds the rounding
of `erfc_asympt_fast`'s evaluation, the row's certificate (`ErfcAsymRowsT`) bounds the polynomial
at `1/x²` against `x erfcx x`, and the polynomial's change from `1/x²` to `U` is at most the bound
`absSum MU Z'` on its derivative times `|U - 1/x²|` (`z_lip`).  `RowT` collects the conditions of a
row that the kernel checks, and `z_row` gives a double-double within `2^-67 M` of `Z (U)`, with
`1/2 ≤ M ≤ 1`, and `Z (U)` within `2^-60` of `x erfcx x`.  `G_bounds` places `x erfcx x` between
`0.49` and `0.57` for `x ≥ 2` from the first two terms of the asymptotic series.
-/

namespace Library.Numerics.Float64.Erfc.ErfcAsymZ

open Real Set CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcAsymPoly ErfcAsymPlan
  ErfcAsymCert ErfcAccMain FmaSpec PolyBound PolyCalculus RealErf ErfcSeries

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)

/-- `x erfcx x` for `x ≥ 2`. -/
theorem G_bounds (x : ℝ) (hx : 2 ≤ x) : 49 / 100 ≤ x * erfcx x ∧ x * erfcx x ≤ 57 / 100 := by
  have hx0 : 0 < x := by linarith
  have e1 : asymSum 1 x = x⁻¹ := by
    norm_num [asymSum, Finset.sum_range_succ, asymCoeff]
  have e2 : asymSum 2 x = x⁻¹ - x⁻¹ ^ 3 / 2 := by
    norm_num [asymSum, Finset.sum_range_succ, asymCoeff]
    ring
  have h1 := erfcx_asym 1 hx0
  have h2 := erfcx_asym 2 hx0
  rw [e1, pow_one, neg_one_mul] at h1
  rw [e2, neg_one_sq, one_mul] at h2
  have hsl := scale_lo
  have hsh := scale_hi
  have hs0 := scale_pos
  have qsl : (112 / 100 : ℝ) ≤ sLo := by
    have : (112 / 100 : ℚ) ≤ sLo := by decide +kernel
    qc this
  have qsh : (sHi : ℝ) ≤ 113 / 100 := by
    have : sHi ≤ (113 / 100 : ℚ) := by decide +kernel
    qc this
  have hxi : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0.ne'
  have ht0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have ht1 : x⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have hup : erfcx x ≤ scale / 2 * x⁻¹ := by linarith
  have hlow : scale / 2 * (x⁻¹ - x⁻¹ ^ 3 / 2) ≤ erfcx x := by linarith
  constructor
  · have k := mul_le_mul_of_nonneg_left hlow hx0.le
    have e3 : x * x⁻¹ ^ 3 = x⁻¹ ^ 2 := by
      calc x * x⁻¹ ^ 3 = (x * x⁻¹) * x⁻¹ ^ 2 := by ring
        _ = x⁻¹ ^ 2 := by rw [hxi, one_mul]
    have e : x * (scale / 2 * (x⁻¹ - x⁻¹ ^ 3 / 2)) = scale / 2 * (1 - x⁻¹ ^ 2 / 2) := by
      calc x * (scale / 2 * (x⁻¹ - x⁻¹ ^ 3 / 2)) = scale / 2 * (x * x⁻¹ - x * x⁻¹ ^ 3 / 2) := by
            ring
        _ = scale / 2 * (1 - x⁻¹ ^ 2 / 2) := by rw [hxi, e3]
    rw [e] at k
    have ht2 : x⁻¹ ^ 2 ≤ 1 / 4 := by nlinarith
    have k2 : scale / 2 * (7 / 8) ≤ scale / 2 * (1 - x⁻¹ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  · have k := mul_le_mul_of_nonneg_left hup hx0.le
    have e : x * (scale / 2 * x⁻¹) = scale / 2 := by
      calc x * (scale / 2 * x⁻¹) = scale / 2 * (x * x⁻¹) := by ring
        _ = scale / 2 := by rw [hxi, mul_one]
    rw [e] at k
    linarith

/-- The change of a polynomial between two arguments of `[-MU, MU]`. -/
theorem z_lip (P : List ℚ) (MU Lip : ℚ) (hMU : 0 ≤ MU) (hLip : absSum MU (derivP P) ≤ Lip)
    {a b : ℝ} (ha : |a| ≤ MU) (hb : |b| ≤ MU) : |eval P a - eval P b| ≤ Lip * |a - b| := by
  have h1 : ∀ t : ℝ, eval [1] t = 1 := fun t => by simp [eval_cons, eval_nil]
  have h0 : ∀ t : ℝ, eval (derivP [1]) t = 0 := fun t => by
    simp [derivP, addP, eval_cons, eval_nil]
  have h := F64DivApprox.ratio_lipschitz P [1] (-(MU : ℝ)) MU Lip
    (fun t _ => by rw [h1]; norm_num)
    (fun t ht => by
      rw [h1, h0, mul_one, mul_zero, sub_zero, one_pow, mul_one]
      have ht' : |t| ≤ (MU : ℝ) := abs_le.mpr ⟨ht.1, ht.2⟩
      exact (abs_eval_le MU hMU (derivP P) t ht').trans (by qc hLip))
    (x := a) (y := b) ⟨(abs_le.mp ha).1, (abs_le.mp ha).2⟩ ⟨(abs_le.mp hb).1, (abs_le.mp hb).2⟩
  rwa [h1, h1, div_one, div_one] at h

/-- The words of a row of `T` in the form the kernel checks. -/
def AsymEntQ (tab : Array UInt64) (o : UInt64) (q : List ℚ) : Prop :=
  (Finite tab[(o + 12).toNat]! ∧ ratOfWord tab[(o + 12).toNat]! = q.getD 12 0) ∧
    (Finite tab[(o + 11).toNat]! ∧ ratOfWord tab[(o + 11).toNat]! = q.getD 11 0) ∧
    (Finite tab[(o + 10).toNat]! ∧ ratOfWord tab[(o + 10).toNat]! = q.getD 10 0) ∧
    (Finite tab[(o + 9).toNat]! ∧ ratOfWord tab[(o + 9).toNat]! = q.getD 9 0) ∧
    (∀ j < 7, Finite tab[(o + 8 - UInt64.ofNat j).toNat]! ∧
      ratOfWord tab[(o + 8 - UInt64.ofNat j).toNat]! = q.getD (8 - j) 0) ∧
    (Finite tab[o.toNat]! ∧ ratOfWord tab[o.toNat]! = q.getD 0 0) ∧
    (Finite tab[(o + 1).toNat]! ∧ ratOfWord tab[(o + 1).toNat]! = q.getD 1 0)

instance (tab : Array UInt64) (o : UInt64) (q : List ℚ) : Decidable (AsymEntQ tab o q) := by
  unfold AsymEntQ; infer_instance

theorem asymEnt_of_q (tab : Array UInt64) (o : UInt64) (q : List ℚ) (h : AsymEntQ tab o q) :
    AsymEnt tab o q := by
  obtain ⟨h12, h11, h10, h9, h8, h0, h1⟩ := h
  exact ⟨ent_of_q _ _ _ h12, ent_of_q _ _ _ h11, ent_of_q _ _ _ h10, ent_of_q _ _ _ h9,
    fun j hj => ent_of_q _ _ _ (h8 j hj), ent_of_q _ _ _ h0, ent_of_q _ _ _ h1⟩

/-- The conditions of row `i` of `T` that the kernel checks, for the bound `MU` on `U`. -/
def RowT (i : ℕ) (MU : ℚ) : Prop :=
  AsymEntQ Erfc.asymTable (13 * UInt64.ofNat i) (tq i) ∧
    AsymHyp (tq i) MU (MU / 2 ^ 50) (asymB (tq i) MU (MU / 2 ^ 50)) ∧
    (asymB (tq i) MU (MU / 2 ^ 50)).f0e ≤ (asymB (tq i) MU (MU / 2 ^ 50)).f0M / 2 ^ 67 ∧
    (asymB (tq i) MU (MU / 2 ^ 50)).f0L ≤ (asymB (tq i) MU (MU / 2 ^ 50)).f0M / 2 ^ 51 ∧
    1 / 2 ≤ (asymB (tq i) MU (MU / 2 ^ 50)).f0M ∧ (asymB (tq i) MU (MU / 2 ^ 50)).f0M ≤ 1 ∧
    1 + 1 / 2 ^ 50 ≤ MU * (loT.getD i 0) ^ 2 ∧ 2 ≤ loT.getD i 0 ∧
    absSum MU (derivP (fastZ (tq i))) ≤ 1

set_option synthInstance.maxSize 4096 in
instance (i : ℕ) (MU : ℚ) : Decidable (RowT i MU) := by
  unfold RowT; infer_instance

theorem asymPoly_eq (q : List ℚ) : asymPoly q = fastZ q := rfl

/-- The polynomial of row `i` of `T` at `U`, within `2^-60` of `x erfcx x`. -/
theorem z_row (hF : FmaNearest) (i : ℕ) (MU : ℚ) (hrow : RowT i MU)
    (hrowL : ∀ y ∈ Icc ((loT.getD i 0 : ℚ) : ℝ) (hiT.getD i 0),
      |eval (fastZ (tq i)) (y ^ 2)⁻¹ - y * erfcx y| ≤ (rhoA : ℝ) * (y * erfcx y))
    (x : ℝ) (hxlo : (loT.getD i 0 : ℝ) ≤ x) (hxhi : x ≤ hiT.getD i 0)
    (uh ul : Float) (huh : ff uh) (hul : ff ul)
    (hU : |fv uh + fv ul - (1 / x) ^ 2| ≤ 14 * u * u * (1 / x) ^ 2)
    (hL : |fv ul| ≤ 4 * u * (1 / x) ^ 2) :
    ∃ M : ℝ, Pr (asymCore Erfc.asymTable (13 * UInt64.ofNat i) uh ul).1
        (asymCore Erfc.asymTable (13 * UInt64.ofNat i) uh ul).2
        (eval (fastZ (tq i)) (fv uh + fv ul)) M (M / 2 ^ 51) (M / 2 ^ 67) ∧
      1 / 2 ≤ M ∧ M ≤ 1 ∧
      |eval (fastZ (tq i)) (fv uh + fv ul) - x * erfcx x| ≤ x * erfcx x / 2 ^ 60 := by
  obtain ⟨hent, hhyp, he, hl, hm1, hm2, hmu, hlo2, hlip⟩ := hrow
  set b := asymB (tq i) MU (MU / 2 ^ 50)
  set lo : ℚ := loT.getD i 0
  have qlo2 : (2 : ℝ) ≤ lo := by qc hlo2
  have hx2 : 2 ≤ x := qlo2.trans hxlo
  have hx0 : 0 < x := by linarith
  have qmu : 1 + 1 / 2 ^ 50 ≤ (MU : ℝ) * lo ^ 2 := by qc hmu
  have hk : (1 / x) ^ 2 * (lo : ℝ) ^ 2 ≤ 1 := by
    rw [← mul_pow, one_div_mul_eq_div]
    have : (lo : ℝ) / x ≤ 1 := by rw [div_le_one hx0]; exact hxlo
    have h0 : (0 : ℝ) ≤ lo / x := div_nonneg (by linarith) hx0.le
    calc ((lo : ℝ) / x) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = 1 := one_pow 2
  have ht0 : 0 ≤ (1 / x) ^ 2 := by positivity
  have hMU0 : (0 : ℝ) ≤ MU := by
    by_contra hn
    push Not at hn
    have : (MU : ℝ) * lo ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn.le (by positivity)
    linarith [show (0 : ℝ) < 1 + 1 / 2 ^ 50 by positivity]
  have hMUt : (1 / x) ^ 2 * (1 + 1 / 2 ^ 50) ≤ MU := by
    calc (1 / x) ^ 2 * (1 + 1 / 2 ^ 50) ≤ (1 / x) ^ 2 * ((MU : ℝ) * lo ^ 2) :=
          mul_le_mul_of_nonneg_left qmu ht0
      _ = ((1 / x) ^ 2 * (lo : ℝ) ^ 2) * MU := by ring
      _ ≤ 1 * MU := mul_le_mul_of_nonneg_right hk hMU0
      _ = MU := one_mul _
  have hUabs : |fv uh + fv ul| ≤ (MU : ℝ) := by
    have := abs_sub_abs_le_abs_sub (fv uh + fv ul) ((1 / x) ^ 2)
    rw [abs_of_nonneg ht0] at this
    have : 14 * u * u * (1 / x) ^ 2 ≤ (1 / x) ^ 2 * (1 / 2 ^ 50) := by
      rw [mul_comm ((1 / x) ^ 2)]; gcongr; norm_num
    linarith
  have hLabs : |fv ul| ≤ ((MU / 2 ^ 50 : ℚ) : ℝ) := by
    push_cast
    refine hL.trans ?_
    have : 4 * u * (1 / x) ^ 2 ≤ (1 / x) ^ 2 * (1 + 1 / 2 ^ 50) / 2 ^ 50 := by
      have : 4 * u ≤ (1 + 1 / 2 ^ 50) / 2 ^ 50 := by norm_num
      calc 4 * u * (1 / x) ^ 2 ≤ (1 + 1 / 2 ^ 50) / 2 ^ 50 * (1 / x) ^ 2 :=
            mul_le_mul_of_nonneg_right this ht0
        _ = (1 / x) ^ 2 * (1 + 1 / 2 ^ 50) / 2 ^ 50 := by ring
    exact this.trans (div_le_div_of_nonneg_right hMUt (by norm_num))
  have hc := asym_core_pr hF Erfc.asymTable (13 * UInt64.ofNat i) uh ul (tq i) MU (MU / 2 ^ 50) b
    hhyp huh hul hUabs hLabs (asymEnt_of_q _ _ _ hent)
  rw [asymPoly_eq] at hc
  have qe : (b.f0e : ℝ) ≤ b.f0M / 2 ^ 67 := by qc he
  have ql : (b.f0L : ℝ) ≤ b.f0M / 2 ^ 51 := by qc hl
  have qm1 : (1 / 2 : ℝ) ≤ b.f0M := by qc hm1
  have qm2 : (b.f0M : ℝ) ≤ 1 := by qc hm2
  refine ⟨b.f0M, hc.mono le_rfl ql qe, qm1, qm2, ?_⟩
  -- the row's certificate and the change from `1/x²` to `U`
  have hr := hrowL x ⟨hxlo, hxhi⟩
  have hxi : (1 / x) ^ 2 = (x ^ 2)⁻¹ := by rw [one_div, inv_pow]
  have hlipq : (absSum MU (derivP (fastZ (tq i))) : ℚ) ≤ 1 := hlip
  have hxa : |(x ^ 2)⁻¹| ≤ (MU : ℝ) := by
    rw [← hxi, abs_of_nonneg ht0]
    linarith
  have hzl := z_lip (fastZ (tq i)) MU 1 (by qc hMU0) hlipq hUabs hxa
  rw [← hxi] at hzl hr
  have hG := G_bounds x hx2
  have k1 : (1 : ℝ) * |fv uh + fv ul - (1 / x) ^ 2| ≤ 14 * u * u * (1 / 4) := by
    rw [one_mul]
    refine hU.trans ?_
    have : (1 / x) ^ 2 ≤ 1 / 4 := by
      rw [div_pow, one_pow]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  push_cast at hzl
  have hρ : (rhoA : ℝ) = 1 / 2 ^ 61 := by unfold rhoA; norm_num
  rw [hρ] at hr
  have t := abs_sub_le (eval (fastZ (tq i)) (fv uh + fv ul)) (eval (fastZ (tq i)) ((1 / x) ^ 2))
    (x * erfcx x)
  have : 14 * u * u * (1 / 4) ≤ x * erfcx x / 2 ^ 61 := by
    have : 14 * u * u * (1 / 4) ≤ 49 / 100 / 2 ^ 61 := by norm_num
    linarith [hG.1]
  linarith

#print axioms G_bounds
#print axioms z_lip
#print axioms asymEnt_of_q
#print axioms z_row

end Library.Numerics.Float64.Erfc.ErfcAsymZ
