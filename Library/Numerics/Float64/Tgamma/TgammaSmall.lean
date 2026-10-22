import Library.Numerics.Float64.Tgamma.TgammaPolyDDD
import Library.Numerics.Float64.Tgamma.TgammaExpr
import Library.Numerics.Float64.Tgamma.TgammaApprox
import Library.Numerics.Float64.Tgamma.TgammaWords

/-!
The fast path of `tgammaWith` from `2 ^ -112` to `1/4` in magnitude.  The polynomial `Q` of degree
15 in plain double arithmetic (`lE`, bounded by `TgammaExpr`), the double-double Horner scheme of
degree 4 that adds `x Q` to its top coefficient (`TgammaPolyDDD.polyDDD_spec`), the reciprocal `1/x`
with its `fma` correction, and their `fastSum` give `1/x + smallPoly x` within a small error, which
`SmallFact` relates to `Γ x`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPoly TgammaPolyDDD TgammaExpr
  TgammaWords

set_option exponentiation.threshold 4096

def x2E : FE := .mul .var .var
def x4E : FE := .mul x2E x2E
def x8E : FE := .mul x4E x4E

/-- `a + x b + x² (c + x d)`, as the code groups it. -/
def quad (a b c d : UInt64) : FE :=
  .add (.add (.const a) (.mul .var (.const b))) (.mul x2E (.add (.const c) (.mul .var (.const d))))

def w (i : ℕ) : UInt64 := smallTable[i]!

/-- `x (c0 + x8 c8)` of the code, with `c0 = q0 + x4 q4` and `c8 = q8 + x4 q12`. -/
def lE : FE :=
  .mul .var (.add (.add (quad (w 10) (w 11) (w 12) (w 13)) (.mul x4E (quad (w 14) (w 15) (w 16) (w 17))))
    (.mul x8E (.add (quad (w 18) (w 19) (w 20) (w 21)) (.mul x4E (quad (w 22) (w 23) (w 24) (w 25))))))

theorem lE_ok : ok lE (1 / 4) = true := by decide +kernel

theorem lE_err : (bnd lE (1 / 4)).2 ≤ 1 / 2 ^ 48 := by decide +kernel

theorem lE_mag : (bnd lE (1 / 4)).1 ≤ 1 / 2 := by decide +kernel

#print axioms lE_ok
#print axioms lE_err

theorem w_finite : ∀ k < 26, Wasm.IEEE64.isFinite smallTable[k]! = true := by decide +kernel

theorem hi_le : ∀ k < 5, PolyBound.qabs (PolyBound.ratOfWord smallTable[2 * k]!) ≤ 1 := by
  decide +kernel

theorem lo_le : ∀ k < 5, PolyBound.qabs (PolyBound.ratOfWord smallTable[2 * k + 1]!) ≤ 1 / 2 ^ 54 := by
  decide +kernel

theorem top_ge : 9 / 10 ≤ PolyBound.qabs (PolyBound.ratOfWord smallTable[8]!) := by decide +kernel

theorem coef_sum : (∑ k ∈ Finset.range 5, PolyBound.qabs (PolyBound.ratOfWord smallTable[2 * k]! +
    PolyBound.ratOfWord smallTable[2 * k + 1]!)) ≤ 9 / 2 := by decide +kernel

theorem abs_rat_le (q B : ℚ) (h : PolyBound.qabs q ≤ B) : |(q : ℝ)| ≤ (B : ℝ) := by
  rw [← qabs_cast]
  exact_mod_cast h

/-- `evalR lE x = x Q(x)` with `Q` the coefficients `smallTable[10..25]`. -/
theorem lE_eval (x : ℝ) :
    evalR lE x = x * PolyBound.eval (TgammaApprox.coeffs smallTable 10 1 16) x := by
  rw [eval_coeffs]
  simp only [evalR, lE, quad, x2E, x4E, x8E, w, TgammaApprox.q, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd, zero_add, pow_zero, pow_one, mul_one]
  ring

/-- The exact Horner value of the small path is `smallPoly`. -/
theorem horner_small (x : ℝ) :
    horner (cDD smallTable 0) 5 (evalR lE x) x 4 = TgammaApprox.smallPoly x := by
  rw [show (4 : ℕ) = 5 - 1 from rfl, horner_eval _ 5 (by norm_num), TgammaApprox.smallPoly,
    eval_append, eval_ddCoeffs, lE_eval]
  have hc : ∀ k ∈ Finset.range 5, cDD smallTable 0 k * x ^ k =
      ((TgammaApprox.q smallTable (0 + 2 * k) + TgammaApprox.q smallTable (0 + 2 * k + 1) : ℚ) : ℝ) *
        x ^ k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [cDD_rat smallTable 0 k (w_finite _ (by simp; omega)) (w_finite _ (by simp; omega))]
    simp [TgammaApprox.q]
  rw [Finset.sum_congr rfl hc]
  simp only [TgammaApprox.ddCoeffs, List.length_map, List.length_range]
  ring

/-- **The double-double polynomial of the small path** within `2 ^ -55` of `smallPoly`. -/
theorem small_poly (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (x : Float) (hx : Finite x.toBits)
    (hX : |value x.toBits| ≤ 1 / 4) :
    Finite (polyDDD smallTable 0 5 x (evalF lE x)).1.toBits ∧
      Finite (polyDDD smallTable 0 5 x (evalF lE x)).2.toBits ∧
      |value (polyDDD smallTable 0 5 x (evalF lE x)).1.toBits +
          value (polyDDD smallTable 0 5 x (evalF lE x)).2.toBits -
          TgammaApprox.smallPoly (value x.toBits)| ≤ 1 / 2 ^ 55 ∧
      |value (polyDDD smallTable 0 5 x (evalF lE x)).2.toBits| ≤ 1 / 2 ^ 43 := by
  have hX' : |value x.toBits| ≤ ((1 / 4 : ℚ) : ℝ) := by push_cast; exact hX
  obtain ⟨hl, hLm⟩ := evalF_approx lE (1 / 4) x hx hX' lE_ok
  set vx := value x.toBits with hvx
  set L := evalR lE vx with hLdef
  have hel : |value (evalF lE x).toBits - L| ≤ 1 / 2 ^ 48 := by
    have h := hl.2
    have : ((bnd lE (1 / 4)).2 : ℝ) ≤ ((1 / 2 ^ 48 : ℚ) : ℝ) := by exact_mod_cast lE_err
    push_cast at this
    linarith
  have hLb : |L| ≤ 1 / 2 := by
    have : ((bnd lE (1 / 4)).1 : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast lE_mag
    push_cast at this
    linarith
  have hlb : |value (evalF lE x).toBits| ≤ 1 := by
    have := abs_sub_abs_le_abs_sub (value (evalF lE x).toBits) L
    linarith [(by norm_num : (1 : ℝ) / 2 + 1 / 2 ^ 48 ≤ 1)]
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have hfh : ∀ k < (5 : UInt64).toNat,
      Finite (Float.ofBits smallTable[(0 : UInt64).toNat + 2 * k]!).toBits := by
    intro k hk
    rw [h0, zero_add]
    exact ofBits_finite _ (w_finite _ (by simp at hk; omega))
  have hfl : ∀ k < (5 : UInt64).toNat,
      Finite (Float.ofBits smallTable[(0 : UInt64).toNat + 2 * k + 1]!).toBits := by
    intro k hk
    rw [h0, zero_add]
    exact ofBits_finite _ (w_finite _ (by simp at hk; omega))
  have hCh : ∀ k < (5 : UInt64).toNat,
      |value (Float.ofBits smallTable[(0 : UInt64).toNat + 2 * k]!).toBits| ≤ 1 := by
    intro k hk
    have hk' : k < 5 := by simpa using hk
    rw [h0, zero_add, ofBits_value _ (w_finite _ (by omega))]
    have := abs_rat_le _ _ (hi_le k hk')
    push_cast at this
    exact this
  have hCl : ∀ k < (5 : UInt64).toNat,
      |value (Float.ofBits smallTable[(0 : UInt64).toNat + 2 * k + 1]!).toBits| ≤ 1 / 2 ^ 54 := by
    intro k hk
    have hk' : k < 5 := by simpa using hk
    rw [h0, zero_add, ofBits_value _ (w_finite _ (by omega))]
    have := abs_rat_le _ _ (lo_le k hk')
    push_cast at this
    exact this
  have htop : |value (evalF lE x).toBits| ≤
      |value (Float.ofBits smallTable[(0 : UInt64).toNat + 2 * ((5 : UInt64).toNat - 1)]!).toBits| := by
    rw [show (0 : UInt64).toNat + 2 * ((5 : UInt64).toNat - 1) = 8 from rfl,
      ofBits_value _ (w_finite 8 (by norm_num)), ← qabs_cast]
    have : ((9 / 10 : ℚ) : ℝ) ≤ ((PolyBound.qabs (PolyBound.ratOfWord smallTable[8]!) : ℚ) : ℝ) := by
      exact_mod_cast top_ge
    push_cast at this
    have := abs_sub_abs_le_abs_sub (value (evalF lE x).toBits) L
    linarith [(by norm_num : (1 : ℝ) / 2 + 1 / 2 ^ 48 ≤ 9 / 10)]
  have hM : ∀ m, m + 1 ≤ (5 : UInt64).toNat → |horner (cDD smallTable 0) (5 : UInt64).toNat L vx m| ≤ 5 := by
    intro m hm
    have h5 : (5 : UInt64).toNat = 5 := rfl
    rw [h5] at hm ⊢
    refine (horner_bound _ 5 L vx (hX.trans (by norm_num)) m hm).trans ?_
    have hs : (∑ k ∈ Finset.range 5, |cDD smallTable 0 k|) ≤ 9 / 2 := by
      have hc : ∀ k ∈ Finset.range 5, |cDD smallTable 0 k| =
          ((PolyBound.qabs (PolyBound.ratOfWord smallTable[2 * k]! +
            PolyBound.ratOfWord smallTable[2 * k + 1]!) : ℚ) : ℝ) := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [cDD_rat smallTable 0 k (w_finite _ (by simp; omega)) (w_finite _ (by simp; omega)),
          qabs_cast]
        simp
      rw [Finset.sum_congr rfl hc, ← Rat.cast_sum]
      calc _ ≤ ((9 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr coef_sum
        _ = 9 / 2 := by norm_num
    linarith
  obtain ⟨h1, h2, h3, h4⟩ := polyDDD_damped hF smallTable 0 5 x (evalF lE x) (by decide)
    (by decide) hfh hfl (1 / 4) 5 1 (1 / 2 ^ 54) (1 / 2 ^ 43) L (1 / 2 ^ 48) 1 hx hX (by norm_num)
    hCh hCl hl.1 hel hlb htop hM
    (by simp only [polyT, polyGrow, show (5 : UInt64).toNat = 5 from rfl]; norm_num)
    (by simp only [polyT, polyEps, polyLow, show (5 : UInt64).toNat = 5 from rfl]; norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨h1, h2, ?_, h4⟩
  have hh : horner (cDD smallTable 0) 5 L vx 4 = TgammaApprox.smallPoly vx := horner_small vx
  rw [show (5 : UInt64).toNat = 5 from rfl, show 5 - 1 = 4 from rfl, hh] at h3
  refine h3.trans ?_
  simp only [polyT, polyEps, polyLow]
  norm_num

#print axioms small_poly

end Library.Numerics.Float64.Tgamma.TgammaSmall
