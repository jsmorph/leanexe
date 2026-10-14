import Verified.Examples.TgammaSmall

/-!
The polynomial of `Tgamma.accurate` below `1/4` in magnitude.  The polynomial `Q` of degree 7 in
plain double arithmetic (`lAccE`, bounded by `TgammaExpr`) and the double-double Horner scheme of
degree 27 that adds `x Q` to its top coefficient (`TgammaPolyDDD.polyDDD_damped`) give
`accSmallPoly x` within `2 ^ -80` (`acc_small_poly`), which `AccSmallFact` relates to `Γ x`.
-/

namespace Verified.Examples.TgammaAccSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPoly TgammaPolyDDD TgammaExpr
  TgammaWords TgammaSmall

set_option exponentiation.threshold 4096

def a (i : ℕ) : UInt64 := accurateTable[i]!

/-- `x (c0 + x4 c4)` of the code, with `c0` and `c4` the groups of four coefficients from entry 56
on. -/
def lAccE : FE :=
  .mul .var (.add (quad (a 56) (a 57) (a 58) (a 59)) (.mul x4E (quad (a 60) (a 61) (a 62) (a 63))))

theorem lAccE_ok : ok lAccE (1 / 4) = true := by decide +kernel

theorem lAccE_err : (bnd lAccE (1 / 4)).2 ≤ 1 / 2 ^ 48 := by decide +kernel

theorem lAccE_mag : (bnd lAccE (1 / 4)).1 ≤ 1 / 2 := by decide +kernel

theorem a_finite : ∀ k < 64, Wasm.IEEE64.isFinite accurateTable[k]! = true := by decide +kernel

theorem hi_le : ∀ k < 28, PolyBound.qabs (PolyBound.ratOfWord accurateTable[2 * k]!) ≤ 2 := by
  decide +kernel

theorem lo_le : ∀ k < 28,
    PolyBound.qabs (PolyBound.ratOfWord accurateTable[2 * k + 1]!) ≤ 1 / 2 ^ 53 := by
  decide +kernel

theorem top_ge : 1 ≤ PolyBound.qabs (PolyBound.ratOfWord accurateTable[54]!) := by decide +kernel

theorem coef_sum : (∑ k ∈ Finset.range 28,
    PolyBound.qabs (PolyBound.ratOfWord accurateTable[2 * k]! +
      PolyBound.ratOfWord accurateTable[2 * k + 1]!)) ≤ 28 := by decide +kernel

/-- `evalR lAccE x = x Q(x)` with `Q` the coefficients `accurateTable[56..63]`. -/
theorem lAccE_eval (x : ℝ) :
    evalR lAccE x = x * PolyBound.eval (TgammaApprox.coeffs accurateTable 56 1 8) x := by
  rw [eval_coeffs]
  simp only [evalR, lAccE, quad, x2E, x4E, a, TgammaApprox.q, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd, zero_add, pow_zero, pow_one, mul_one]
  ring

/-- The exact Horner value of the accurate path below `1/4` is `accSmallPoly`. -/
theorem horner_acc_small (x : ℝ) :
    horner (cDD accurateTable 0) 28 (evalR lAccE x) x 27 = TgammaApprox.accSmallPoly x := by
  rw [show (27 : ℕ) = 28 - 1 from rfl, horner_eval _ 28 (by norm_num), TgammaApprox.accSmallPoly,
    eval_append, eval_ddCoeffs, lAccE_eval]
  have hc : ∀ k ∈ Finset.range 28, cDD accurateTable 0 k * x ^ k =
      ((TgammaApprox.q accurateTable (0 + 2 * k) +
        TgammaApprox.q accurateTable (0 + 2 * k + 1) : ℚ) : ℝ) * x ^ k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [cDD_rat accurateTable 0 k (a_finite _ (by simp; omega)) (a_finite _ (by simp; omega))]
    simp [TgammaApprox.q]
  rw [Finset.sum_congr rfl hc]
  simp only [TgammaApprox.ddCoeffs, List.length_map, List.length_range]
  ring

/-- **The double-double polynomial of the accurate path below `1/4`** within `2 ^ -80` of
`accSmallPoly`. -/
theorem acc_small_poly (hF : FmaSpec.FmaNearest) (x : Float) (hx : Finite x.toBits)
    (hX : |value x.toBits| ≤ 1 / 4) :
    Finite (polyDDD accurateTable 0 28 x (evalF lAccE x)).1.toBits ∧
      Finite (polyDDD accurateTable 0 28 x (evalF lAccE x)).2.toBits ∧
      |value (polyDDD accurateTable 0 28 x (evalF lAccE x)).1.toBits +
          value (polyDDD accurateTable 0 28 x (evalF lAccE x)).2.toBits -
          TgammaApprox.accSmallPoly (value x.toBits)| ≤ 1 / 2 ^ 80 ∧
      |value (polyDDD accurateTable 0 28 x (evalF lAccE x)).2.toBits| ≤ 1 / 2 ^ 38 := by
  have hX' : |value x.toBits| ≤ ((1 / 4 : ℚ) : ℝ) := by push_cast; exact hX
  obtain ⟨hl, hLm⟩ := evalF_approx lAccE (1 / 4) x hx hX' lAccE_ok
  set vx := value x.toBits with hvx
  set L := evalR lAccE vx with hLdef
  have hel : |value (evalF lAccE x).toBits - L| ≤ 1 / 2 ^ 48 := by
    have h := hl.2
    have : ((bnd lAccE (1 / 4)).2 : ℝ) ≤ ((1 / 2 ^ 48 : ℚ) : ℝ) := by exact_mod_cast lAccE_err
    push_cast at this
    linarith
  have hLb : |L| ≤ 1 / 2 := by
    have : ((bnd lAccE (1 / 4)).1 : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast lAccE_mag
    push_cast at this
    linarith
  have hlb : |value (evalF lAccE x).toBits| ≤ 1 := by
    have := abs_sub_abs_le_abs_sub (value (evalF lAccE x).toBits) L
    linarith [(by norm_num : (1 : ℝ) / 2 + 1 / 2 ^ 48 ≤ 1)]
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have hfh : ∀ k < (28 : UInt64).toNat,
      Finite (Float.ofBits accurateTable[(0 : UInt64).toNat + 2 * k]!).toBits := by
    intro k hk
    rw [h0, zero_add]
    exact ofBits_finite _ (a_finite _ (by simp at hk; omega))
  have hfl : ∀ k < (28 : UInt64).toNat,
      Finite (Float.ofBits accurateTable[(0 : UInt64).toNat + 2 * k + 1]!).toBits := by
    intro k hk
    rw [h0, zero_add]
    exact ofBits_finite _ (a_finite _ (by simp at hk; omega))
  have hCh : ∀ k < (28 : UInt64).toNat,
      |value (Float.ofBits accurateTable[(0 : UInt64).toNat + 2 * k]!).toBits| ≤ 2 := by
    intro k hk
    have hk' : k < 28 := by simpa using hk
    rw [h0, zero_add, ofBits_value _ (a_finite _ (by omega))]
    have := abs_rat_le _ _ (hi_le k hk')
    push_cast at this
    exact this
  have hCl : ∀ k < (28 : UInt64).toNat,
      |value (Float.ofBits accurateTable[(0 : UInt64).toNat + 2 * k + 1]!).toBits| ≤
        1 / 2 ^ 53 := by
    intro k hk
    have hk' : k < 28 := by simpa using hk
    rw [h0, zero_add, ofBits_value _ (a_finite _ (by omega))]
    have := abs_rat_le _ _ (lo_le k hk')
    push_cast at this
    exact this
  have htop : |value (evalF lAccE x).toBits| ≤
      |value (Float.ofBits
        accurateTable[(0 : UInt64).toNat + 2 * ((28 : UInt64).toNat - 1)]!).toBits| := by
    rw [show (0 : UInt64).toNat + 2 * ((28 : UInt64).toNat - 1) = 54 from rfl,
      ofBits_value _ (a_finite 54 (by norm_num)), ← qabs_cast]
    have : ((1 : ℚ) : ℝ) ≤ ((PolyBound.qabs (PolyBound.ratOfWord accurateTable[54]!) : ℚ) : ℝ) := by
      exact_mod_cast top_ge
    push_cast at this
    linarith
  have hM : ∀ m, m + 1 ≤ (28 : UInt64).toNat →
      |horner (cDD accurateTable 0) (28 : UInt64).toNat L vx m| ≤ 29 := by
    intro m hm
    have h28 : (28 : UInt64).toNat = 28 := rfl
    rw [h28] at hm ⊢
    refine (horner_bound _ 28 L vx (hX.trans (by norm_num)) m hm).trans ?_
    have hs : (∑ k ∈ Finset.range 28, |cDD accurateTable 0 k|) ≤ 28 := by
      have hc : ∀ k ∈ Finset.range 28, |cDD accurateTable 0 k| =
          ((PolyBound.qabs (PolyBound.ratOfWord accurateTable[2 * k]! +
            PolyBound.ratOfWord accurateTable[2 * k + 1]!) : ℚ) : ℝ) := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [cDD_rat accurateTable 0 k (a_finite _ (by simp; omega)) (a_finite _ (by simp; omega)),
          qabs_cast]
        simp
      rw [Finset.sum_congr rfl hc, ← Rat.cast_sum]
      calc _ ≤ ((28 : ℚ) : ℝ) := Rat.cast_le.mpr coef_sum
        _ = 28 := by norm_num
    linarith
  obtain ⟨h1, h2, h3, h4⟩ := polyDDD_damped hF accurateTable 0 28 x (evalF lAccE x) (by decide)
    (by decide) hfh hfl (1 / 4) 29 2 (1 / 2 ^ 53) (1 / 2 ^ 38) L (1 / 2 ^ 48) 1 hx hX (by norm_num)
    hCh hCl hl.1 hel hlb htop hM
    (by simp only [polyT, polyGrow, show (28 : UInt64).toNat = 28 from rfl]; norm_num)
    (by simp only [polyT, polyEps, polyLow, show (28 : UInt64).toNat = 28 from rfl]; norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨h1, h2, ?_, h4⟩
  have hh : horner (cDD accurateTable 0) 28 L vx 27 = TgammaApprox.accSmallPoly vx :=
    horner_acc_small vx
  rw [show (28 : UInt64).toNat = 28 from rfl, show 28 - 1 = 27 from rfl, hh] at h3
  refine h3.trans ?_
  simp only [polyT, polyEps, polyLow]
  norm_num

#print axioms lAccE_ok
#print axioms acc_small_poly

end Verified.Examples.TgammaAccSmall
