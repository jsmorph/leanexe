import Library.Numerics.Float64.Tgamma.TgammaAsym5

/-!
**`Tgamma.asLgammaAsym`** within `2 ^ -60` of `log Γ X` for `X = xh + xl` with `4 ≤ xh ≤ 186`,
`4 ≤ X ≤ 186`, and `|xl| ≤ 2 ^ -44` (`asLgammaAsym_spec`).  `asym_gen` writes the code with its
two branches as `TgammaAsym4.hiBranch` and `TgammaAsym5.loBranch`, whose states satisfy
`TgammaAsym4.BranchOK` within `6 · 2 ^ -63`.  The final product with `zh + zl ≈ 1/X` and the sum
add about `2 ^ -66`.  The result lies in `[1, 1000]` with a low part below `2 ^ -14`, the range
that `TgammaExpdSpec.asExpd_spec` takes: `log Γ X ≥ log 6 > 3/2`, and the high part of the first
product stays below `800`.  The theorem takes `asLogd`'s specification (`TgammaAsym1.LogdSpec`) and
`StirlingFact` as hypotheses.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAsym6
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaAsym1 TgammaAsym3
  TgammaAsym4 TgammaAsym5

set_option exponentiation.threshold 4096

/-- The code of `asLgammaAsym` with its branches as `hiBranch` and `loBranch`. -/
theorem asym_gen (logTab tab : Array UInt64) (xh xl : Float) :
    asLgammaAsym logTab tab xh xl =
      (let zh := 1.0 / xh
       let dz := xl * zh
       let zl := (Library.Numerics.Arithmetic.Fma.Fma.fma zh (-xh) 1.0 - dz) * zh
       let (lh, ll) := asLogd logTab xh
       let (lh, ll) := mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)
       let (z2h, z2l) := mulDD zh zl zh zl
       let (lh, ll, fh, fl) :=
         if xh > 11.5 then hiBranch tab lh ll z2h else loBranch tab lh ll z2h z2l
       let (fh, fl) := mulDD zh zl fh fl
       fastSum lh ll fh fl) := rfl

theorem c115_bits : (11.5 : Float).toBits = 0x4027000000000000 := rfl

theorem c115_finite : Finite (11.5 : Float).toBits := by
  rw [c115_bits]; unfold CodeLib.IEEE64.Finite; decide

theorem c115_value : value (11.5 : Float).toBits = 23 / 2 := by
  rw [c115_bits, TgammaSpecial.lit_value _ (23 / 2) (by decide +kernel)]
  norm_num

/-- `log Γ X > 3/2` for `X ≥ 4`, since `Γ X ≥ Γ 4 = 6` and `e ^ 3 < 36`. -/
theorem lgamma_gt (X : ℝ) (hX : 4 ≤ X) : 3 / 2 < Real.log (Real.Gamma X) := by
  have h4 : Real.Gamma 4 = 6 := by
    have := Real.Gamma_nat_eq_factorial 3
    rw [show ((3 : ℕ) : ℝ) + 1 = 4 by norm_num, show Nat.factorial 3 = 6 from rfl] at this
    rw [this]
    norm_num
  have hmono : Real.Gamma 4 ≤ Real.Gamma X :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr (by norm_num))
      (Set.mem_Ici.mpr (by linarith)) hX
  have h36 : Real.exp 3 < 36 := by
    have h := Real.exp_one_lt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h3]
    have : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 3
    linarith [(by norm_num : (2.7182818286 : ℝ) ^ 3 < 36)]
  have hl36 : 3 < Real.log 36 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 36)]
    exact h36
  have hl6 : Real.log 36 = 2 * Real.log 6 := by
    rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hle : Real.log 6 ≤ Real.log (Real.Gamma X) :=
    Real.log_le_log (by norm_num) (by linarith)
  linarith

/-- **`asLgammaAsym`** within `2 ^ -60` of `log Γ (xh + xl)`. -/
theorem asLgammaAsym_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLog : LogdSpec)
    (hS : TgammaApprox.StirlingFact) (xh xl : Float) (hxh : Finite xh.toBits)
    (hxl : Finite xl.toBits) (h4 : 4 ≤ value xh.toBits) (h186 : value xh.toBits ≤ 186)
    (hX4 : 4 ≤ value xh.toBits + value xl.toBits) (hX186 : value xh.toBits + value xl.toBits ≤ 186)
    (hxlb : |value xl.toBits| ≤ 1 / 2 ^ 44) :
    Finite (asLgammaAsym logdTable asymTable xh xl).1.toBits ∧
      Finite (asLgammaAsym logdTable asymTable xh xl).2.toBits ∧
      |value (asLgammaAsym logdTable asymTable xh xl).1.toBits +
          value (asLgammaAsym logdTable asymTable xh xl).2.toBits -
          Real.log (Real.Gamma (value xh.toBits + value xl.toBits))| ≤ 1 / 2 ^ 60 ∧
      |value (asLgammaAsym logdTable asymTable xh xl).2.toBits| ≤ 1 / 2 ^ 14 ∧
      1 ≤ value (asLgammaAsym logdTable asymTable xh xl).1.toBits +
        value (asLgammaAsym logdTable asymTable xh xl).2.toBits ∧
      value (asLgammaAsym logdTable asymTable xh xl).1.toBits +
        value (asLgammaAsym logdTable asymTable xh xl).2.toBits ≤ 1000 := by
  rw [asym_gen]
  dsimp only
  -- the reciprocal
  obtain ⟨hzf, hlf, -, hzX, hsum, hzl⟩ := asym_recip hF xh xl hxh hxl h4 h186 hxlb
  -- the logarithm and the first product
  obtain ⟨hlhf, hllf, hle, hllb⟩ := hLog xh hxh h4 h186
  generalize asLogd logdTable xh = L at hlhf hllf hle hllb ⊢
  obtain ⟨lh, ll⟩ := L
  dsimp only at hlhf hllf hle hllb ⊢
  obtain ⟨hPf1, hPf2, hPe, hPl, hP1, hP2⟩ :=
    asym_front hF xh xl lh ll hxh hxl hlhf hllf h4 h186 hX4 hX186 hxlb hle hllb
  generalize mulDD (xh - 0.5) xl (lh - 1.0) (ll + xl * (1.0 / xh)) = P at hPf1 hPf2 hPe hPl hP1 hP2 ⊢
  obtain ⟨Ph, Pl⟩ := P
  dsimp only at hPf1 hPf2 hPe hPl hP1 hP2 ⊢
  generalize (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / xh) (-xh) 1.0 - xl * (1.0 / xh)) * (1.0 / xh) = zl at hlf hsum hzl ⊢
  -- `Z = 1/X` and the square
  have hX0 : 0 < value xh.toBits + value xl.toBits := by linarith
  have hZ0 : 0 < 1 / (value xh.toBits + value xl.toBits) := one_div_pos.mpr hX0
  have hZlo : 1 / 2 ^ 9 ≤ 1 / (value xh.toBits + value xl.toBits) := by
    rw [div_le_div_iff₀ (by norm_num) hX0]
    linarith
  have hZhi : 1 / (value xh.toBits + value xl.toBits) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hX0 (by norm_num)]
    linarith
  obtain ⟨hqf1, hqf2, hqe, hqh, hql⟩ := asym_square hF (1.0 / xh) zl hzf hlf _ hZlo
    (by linarith only [hZhi]) hzX hsum hzl
  generalize mulDD (1.0 / xh) zl (1.0 / xh) zl = Q at hqf1 hqf2 hqe hqh hql ⊢
  obtain ⟨u, ul⟩ := Q
  dsimp only at hqf1 hqf2 hqe hqh hql ⊢
  -- the branches
  have hB : BranchOK (value xh.toBits + value xl.toBits)
      (if xh > 11.5 then hiBranch asymTable Ph Pl u else loBranch asymTable Ph Pl u ul) := by
    obtain ⟨he1, he2⟩ := abs_le.mp hxlb
    by_cases hc : xh > 11.5
    · rw [ite_eq_left hc]
      have hc' : 23 / 2 < value xh.toBits := by
        rw [← c115_value]; exact (F64UpperWord.float_lt_iff _ _ c115_finite hxh).mp hc
      exact asym_hi hS.1 Ph Pl u hPf1 hPf2 hqf1 _ (by linarith) hX186 hPe hPl hP1 hP2 hqh
    · rw [ite_eq_right hc]
      have hc' : value xh.toBits ≤ 23 / 2 := by
        rw [← c115_value]
        exact not_lt.mp (fun h => hc ((F64UpperWord.float_lt_iff _ _ c115_finite hxh).mpr h))
      exact asym_lo hF hS.2 Ph Pl u ul hPf1 hPf2 hqf1 hqf2 _ hX4 (by linarith) hPe hPl hP1 hP2
        hqh hqe hql
  generalize (if xh > 11.5 then hiBranch asymTable Ph Pl u else loBranch asymTable Ph Pl u ul) = t
    at hB ⊢
  obtain ⟨lh', ll', fh, fl⟩ := t
  unfold BranchOK at hB
  dsimp only at hB ⊢
  obtain ⟨hlf', hllf', hfhf, hflf, hBe, hlh1, hlh2, hllb', hfhb, hflb⟩ := hB
  -- the product with `zh + zl`
  have hzhb : |value (1.0 / xh).toBits| ≤ 1 / 4 + 1 / 2 ^ 40 := by
    have := abs_sub_abs_le_abs_sub (value (1.0 / xh).toBits) (1 / (value xh.toBits + value xl.toBits))
    rw [abs_of_pos hZ0] at this
    linarith only [this, hzX, hZhi, hZ0]
  have hzlb : |value zl.toBits| ≤ 1 / 4 / 2 ^ 44 := by
    have : 1 / (value xh.toBits + value xl.toBits) / 2 ^ 44 ≤ 1 / 4 / 2 ^ 44 :=
      div_le_div_of_nonneg_right hZhi (by norm_num)
    linarith only [this, hzl]
  have hzh0 := abs_nonneg (value (1.0 / xh).toBits)
  have hzl0 := abs_nonneg (value zl.toBits)
  obtain ⟨hg1f, hg2f, hge, hg2b, hg1b⟩ := mulDD_spec hF (1.0 / xh) zl fh fl hzf hlf hfhf hflf
    (1 / 10 * (1 / 4 + 1 / 2 ^ 40)) (1 / 10 * (1 / 4 / 2 ^ 44)) (1 / 2 ^ 50 * (1 / 4 + 1 / 2 ^ 40))
    (1 / 2 ^ 50 * (1 / 4 / 2 ^ 44))
    (mul_le_mul hfhb hzhb hzh0 (by norm_num)) (mul_le_mul hfhb hzlb hzl0 (by norm_num))
    (mul_le_mul hflb hzhb hzh0 (by norm_num)) (mul_le_mul hflb hzlb hzl0 (by norm_num))
    (by norm_num) (by norm_num)
  generalize mulDD (1.0 / xh) zl fh fl = g at hg1f hg2f hge hg2b hg1b ⊢
  obtain ⟨g1, g2⟩ := g
  dsimp only at hg1f hg2f hge hg2b hg1b ⊢
  have hg2 : |value g2.toBits| ≤ 1 / 2 ^ 49 := hg2b.trans (by norm_num)
  have hg1 : |value g1.toBits| ≤ 1 / 39 := hg1b.trans (by norm_num)
  have hge' : |value g1.toBits + value g2.toBits -
      (value (1.0 / xh).toBits + value zl.toBits) * (value fh.toBits + value fl.toBits)| ≤
      1 / 2 ^ 95 := hge.trans (by norm_num)
  -- the final sum
  obtain ⟨hr1f, hr2f, hre, hr2b⟩ := fastSum_spec lh' ll' g1 g2 hlf' hllf' hg1f hg2f
    (by rw [abs_of_pos (show (0 : ℝ) < value lh'.toBits by linarith only [hlh1])]
        linarith only [hg1, hlh1, (by norm_num : (1 : ℝ) / 39 ≤ 1)])
    (by rw [abs_of_pos (show (0 : ℝ) < value lh'.toBits by linarith only [hlh1])]
        linarith only [hlh2, (by norm_num : (800 : ℝ) < 2 ^ 898)])
    (3 / 4 / 2 ^ 14 + 1 / 2 ^ 49) (by linarith only [hllb', hg2]) (by norm_num)
  generalize fastSum lh' ll' g1 g2 = r at hr1f hr2f hre hr2b ⊢
  obtain ⟨r1, r2⟩ := r
  dsimp only at hr1f hr2f hre hr2b ⊢
  obtain ⟨hl1, hl2⟩ := abs_le.mp hllb'
  obtain ⟨hg11, hg12⟩ := abs_le.mp hg1
  obtain ⟨hg21, hg22⟩ := abs_le.mp hg2
  have hr1b : |value r1.toBits| ≤ 802 := by
    obtain ⟨he1, he2⟩ := abs_le.mp hre
    obtain ⟨hk1, hk2⟩ := abs_le.mp hr2b
    rcases abs_cases (value r1.toBits) with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rw [ha] at he1 he2 hk1 hk2 ⊢ <;>
      linarith only [he1, he2, hk1, hk2, hlh1, hlh2, hl1, hl2, hg11, hg12, hg21, hg22]
  have hre' : |value r1.toBits + value r2.toBits -
      (value lh'.toBits + value ll'.toBits + (value g1.toBits + value g2.toBits))| ≤ 1 / 2 ^ 65 := by
    have : |value r1.toBits| / 2 ^ 52 ≤ 802 / 2 ^ 52 := div_le_div_of_nonneg_right hr1b (by norm_num)
    have h2 : (3 * (3 / 4 / 2 ^ 14 + 1 / 2 ^ 49) + |value r1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) /
        2 ^ 53 ≤ (3 * (3 / 4 / 2 ^ 14 + 1 / 2 ^ 49) + 802 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith only [this]) (by norm_num)
    linarith only [hre, h2, (by norm_num : (3 * ((3 : ℝ) / 4 / 2 ^ 14 + 1 / 2 ^ 49) + 802 / 2 ^ 52 +
      1 / 2 ^ 1074) / 2 ^ 53 ≤ 1 / 2 ^ 65)]
  have hr2 : |value r2.toBits| ≤ 1 / 2 ^ 14 := by
    have : |value r1.toBits| / 2 ^ 51 ≤ 802 / 2 ^ 51 := div_le_div_of_nonneg_right hr1b (by norm_num)
    linarith only [hr2b, this, (by norm_num : ((3 : ℝ) / 4 / 2 ^ 14 + 1 / 2 ^ 49) * (1 + 1 / 2 ^ 51) +
      802 / 2 ^ 51 + 1 / 2 ^ 1073 ≤ 1 / 2 ^ 14)]
  -- the error
  have hzz : |(value (1.0 / xh).toBits + value zl.toBits - 1 / (value xh.toBits + value xl.toBits)) *
      (value fh.toBits + value fl.toBits)| ≤ 1 / 4 / 2 ^ 78 * (1 / 10 + 1 / 2 ^ 50) := by
    rw [abs_mul]
    have h1 : 1 / (value xh.toBits + value xl.toBits) / 2 ^ 78 ≤ 1 / 4 / 2 ^ 78 :=
      div_le_div_of_nonneg_right hZhi (by norm_num)
    refine mul_le_mul (by linarith only [hsum, h1]) ?_ (abs_nonneg _) (by norm_num)
    linarith only [abs_add_le (value fh.toBits) (value fl.toBits), hfhb, hflb]
  have hsplit : value r1.toBits + value r2.toBits -
      Real.log (Real.Gamma (value xh.toBits + value xl.toBits)) =
      (value r1.toBits + value r2.toBits -
        (value lh'.toBits + value ll'.toBits + (value g1.toBits + value g2.toBits))) +
      (value g1.toBits + value g2.toBits -
        (value (1.0 / xh).toBits + value zl.toBits) * (value fh.toBits + value fl.toBits)) +
      (value (1.0 / xh).toBits + value zl.toBits - 1 / (value xh.toBits + value xl.toBits)) *
        (value fh.toBits + value fl.toBits) +
      (value lh'.toBits + value ll'.toBits +
        1 / (value xh.toBits + value xl.toBits) * (value fh.toBits + value fl.toBits) -
        Real.log (Real.Gamma (value xh.toBits + value xl.toBits))) := by ring
  have hE : |value r1.toBits + value r2.toBits -
      Real.log (Real.Gamma (value xh.toBits + value xl.toBits))| ≤ 1 / 2 ^ 60 := by
    rw [hsplit]
    refine (abs4 hre' hge' hzz hBe).trans ?_
    norm_num
  have hLG := lgamma_gt _ hX4
  obtain ⟨hE1, hE2⟩ := abs_le.mp hE
  obtain ⟨hR1, hR2⟩ := abs_le.mp hre'
  refine ⟨hr1f, hr2f, hE, hr2, ?_, ?_⟩
  · linarith only [hE1, hLG, (by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1 / 2)]
  · linarith only [hR2, hlh2, hl2, hg12, hg22, (by norm_num : (1 : ℝ) / 2 ^ 65 ≤ 1)]

#print axioms lgamma_gt
#print axioms asLgammaAsym_spec

end Library.Numerics.Float64.Tgamma.TgammaAsym6
