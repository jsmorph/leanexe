import Library.Numerics.Float64.Tgamma.TgammaPolyDDD
import Library.Numerics.Float64.Tgamma.TgammaExpr
import Library.Numerics.Float64.Tgamma.TgammaApprox
import Library.Numerics.Float64.Tgamma.TgammaWords
import Library.Numerics.Float64.Tgamma.TgammaSmall

/-!
The polynomial of `tgammaWith` on `(-3, 4)`, in `d = x - (i + 7/2)` with `|d| ≤ 1/2 + 2 ^ -50`.
The tail `d Q(d)` of degree 8 in plain double arithmetic (`flE`, bounded by `TgammaExpr`) enters the
top coefficient of the double-double Horner scheme of degree 9 (`TgammaPolyDDD.polyDDD_damped`), and
the result lies within `2 ^ -72` of `mainPoly d` (`main_poly`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaMainPoly
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPoly TgammaPolyDDD TgammaExpr
  TgammaWords

set_option exponentiation.threshold 4096

def w (i : ℕ) : UInt64 := mainTable[i]!

/-- The bound on `|d|`. -/
def D : ℚ := 1 / 2 + 1 / 2 ^ 50

def d2E : FE := .mul .var .var
def d4E : FE := .mul d2E d2E

/-- `a + d b`. -/
def pairE (a b : UInt64) : FE := .add (.const a) (.mul .var (.const b))

/-- `d ((c46 + d c47) + d² (c48 + d c49) + d⁴ ((c50 + d c51) + d² (c52 + d c53)))`, as the code
groups it. -/
def flE : FE :=
  .mul .var (.add (.add (pairE (w 46) (w 47)) (.mul d2E (pairE (w 48) (w 49))))
    (.mul d4E (.add (pairE (w 50) (w 51)) (.mul d2E (pairE (w 52) (w 53))))))

theorem flE_ok : ok flE D = true := by decide +kernel

theorem flE_err : (bnd flE D).2 ≤ 1 / 2 ^ 64 := by decide +kernel

theorem flE_mag : (bnd flE D).1 ≤ 1 / 2 ^ 13 := by decide +kernel

#print axioms flE_ok
#print axioms flE_err

theorem w_finite : ∀ k < 54, Wasm.IEEE64.isFinite mainTable[k]! = true := by decide +kernel

theorem hi_le : ∀ k < 10, PolyBound.qabs (PolyBound.ratOfWord mainTable[2 * k]!) ≤ 4 := by
  decide +kernel

theorem lo_le : ∀ k < 10, PolyBound.qabs (PolyBound.ratOfWord mainTable[2 * k + 1]!) ≤ 1 / 2 ^ 52 := by
  decide +kernel

theorem top_ge : 1 / 2000 ≤ PolyBound.qabs (PolyBound.ratOfWord mainTable[18]!) := by decide +kernel

theorem coef_sum : (∑ k ∈ Finset.range 10, PolyBound.qabs (PolyBound.ratOfWord mainTable[2 * k]! +
    PolyBound.ratOfWord mainTable[2 * k + 1]!)) ≤ 117 / 10 := by decide +kernel

/-- `evalR flE d = d Q(d)` with `Q` the coefficients `mainTable[46..53]`. -/
theorem flE_eval (d : ℝ) :
    evalR flE d = d * PolyBound.eval (TgammaApprox.coeffs mainTable 46 1 8) d := by
  rw [eval_coeffs]
  simp only [evalR, flE, pairE, d2E, d4E, w, TgammaApprox.q, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd, zero_add, pow_zero, pow_one, mul_one]
  ring

/-- The exact Horner value of the main path is `mainPoly`. -/
theorem horner_main (d : ℝ) :
    horner (cDD mainTable 0) 10 (evalR flE d) d 9 = TgammaApprox.mainPoly d := by
  rw [show (9 : ℕ) = 10 - 1 from rfl, horner_eval _ 10 (by norm_num), TgammaApprox.mainPoly,
    eval_append, eval_ddCoeffs, flE_eval]
  have hc : ∀ k ∈ Finset.range 10, cDD mainTable 0 k * d ^ k =
      ((TgammaApprox.q mainTable (0 + 2 * k) + TgammaApprox.q mainTable (0 + 2 * k + 1) : ℚ) : ℝ) *
        d ^ k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [cDD_rat mainTable 0 k (w_finite _ (by simp; omega)) (w_finite _ (by simp; omega))]
    simp [TgammaApprox.q]
  rw [Finset.sum_congr rfl hc]
  simp only [TgammaApprox.ddCoeffs, List.length_map, List.length_range]
  ring

/-- **The double-double polynomial of the main path** within `2 ^ -72` of `mainPoly`. -/
theorem main_poly (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (d : Float) (hd : Finite d.toBits)
    (hD : |value d.toBits| ≤ 1 / 2 + 1 / 2 ^ 50) :
    Finite (polyDDD mainTable 0 10 d (evalF flE d)).1.toBits ∧
      Finite (polyDDD mainTable 0 10 d (evalF flE d)).2.toBits ∧
      |value (polyDDD mainTable 0 10 d (evalF flE d)).1.toBits +
          value (polyDDD mainTable 0 10 d (evalF flE d)).2.toBits -
          TgammaApprox.mainPoly (value d.toBits)| ≤ 1 / 2 ^ 72 ∧
      |value (polyDDD mainTable 0 10 d (evalF flE d)).2.toBits| ≤ 1 / 2 ^ 42 := by
  have hD' : |value d.toBits| ≤ (D : ℝ) := by rw [D]; push_cast; exact hD
  obtain ⟨hl, hLm⟩ := evalF_approx flE D d hd hD' flE_ok
  set vd := value d.toBits with hvd
  set L := evalR flE vd with hLdef
  have hel : |value (evalF flE d).toBits - L| ≤ 1 / 2 ^ 64 := by
    have h := hl.2
    have : ((bnd flE D).2 : ℝ) ≤ ((1 / 2 ^ 64 : ℚ) : ℝ) := by exact_mod_cast flE_err
    push_cast at this
    linarith
  have hLb : |L| ≤ 1 / 2 ^ 13 := by
    have : ((bnd flE D).1 : ℝ) ≤ ((1 / 2 ^ 13 : ℚ) : ℝ) := by exact_mod_cast flE_mag
    push_cast at this
    linarith
  have hlb : |value (evalF flE d).toBits| ≤ 1 / 2 ^ 12 := by
    have := abs_sub_abs_le_abs_sub (value (evalF flE d).toBits) L
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 13 + 1 / 2 ^ 64 ≤ 1 / 2 ^ 12)]
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have hfh : ∀ k < (10 : UInt64).toNat,
      Finite (Float.ofBits mainTable[(0 : UInt64).toNat + 2 * k]!).toBits := by
    intro k hk
    rw [h0, zero_add]
    exact ofBits_finite _ (w_finite _ (by simp at hk; omega))
  have hfl : ∀ k < (10 : UInt64).toNat,
      Finite (Float.ofBits mainTable[(0 : UInt64).toNat + 2 * k + 1]!).toBits := by
    intro k hk
    rw [h0, zero_add]
    exact ofBits_finite _ (w_finite _ (by simp at hk; omega))
  have hCh : ∀ k < (10 : UInt64).toNat,
      |value (Float.ofBits mainTable[(0 : UInt64).toNat + 2 * k]!).toBits| ≤ 4 := by
    intro k hk
    have hk' : k < 10 := by simpa using hk
    rw [h0, zero_add, ofBits_value _ (w_finite _ (by omega))]
    have := TgammaSmall.abs_rat_le _ _ (hi_le k hk')
    push_cast at this
    exact this
  have hCl : ∀ k < (10 : UInt64).toNat,
      |value (Float.ofBits mainTable[(0 : UInt64).toNat + 2 * k + 1]!).toBits| ≤ 1 / 2 ^ 52 := by
    intro k hk
    have hk' : k < 10 := by simpa using hk
    rw [h0, zero_add, ofBits_value _ (w_finite _ (by omega))]
    have := TgammaSmall.abs_rat_le _ _ (lo_le k hk')
    push_cast at this
    exact this
  have htop : |value (evalF flE d).toBits| ≤
      |value (Float.ofBits mainTable[(0 : UInt64).toNat + 2 * ((10 : UInt64).toNat - 1)]!).toBits| := by
    rw [show (0 : UInt64).toNat + 2 * ((10 : UInt64).toNat - 1) = 18 from rfl,
      ofBits_value _ (w_finite 18 (by norm_num)), ← qabs_cast]
    have : ((1 / 2000 : ℚ) : ℝ) ≤ ((PolyBound.qabs (PolyBound.ratOfWord mainTable[18]!) : ℚ) : ℝ) := by
      exact_mod_cast top_ge
    push_cast at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 12 ≤ 1 / 2000)]
  have hM : ∀ m, m + 1 ≤ (10 : UInt64).toNat →
      |horner (cDD mainTable 0) (10 : UInt64).toNat L vd m| ≤ 12 := by
    intro m hm
    have h10 : (10 : UInt64).toNat = 10 := rfl
    rw [h10] at hm ⊢
    refine (horner_bound _ 10 L vd (hD.trans (by norm_num)) m hm).trans ?_
    have hs : (∑ k ∈ Finset.range 10, |cDD mainTable 0 k|) ≤ 117 / 10 := by
      have hc : ∀ k ∈ Finset.range 10, |cDD mainTable 0 k| =
          ((PolyBound.qabs (PolyBound.ratOfWord mainTable[2 * k]! +
            PolyBound.ratOfWord mainTable[2 * k + 1]!) : ℚ) : ℝ) := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [cDD_rat mainTable 0 k (w_finite _ (by simp; omega)) (w_finite _ (by simp; omega)),
          qabs_cast]
        simp
      rw [Finset.sum_congr rfl hc, ← Rat.cast_sum]
      calc _ ≤ ((117 / 10 : ℚ) : ℝ) := Rat.cast_le.mpr coef_sum
        _ = 117 / 10 := by norm_num
    linarith [(by norm_num : (117 : ℝ) / 10 + 1 / 2 ^ 13 ≤ 12)]
  obtain ⟨h1, h2, h3, h4⟩ := polyDDD_damped hF mainTable 0 10 d (evalF flE d) (by decide)
    (by decide) hfh hfl (1 / 2 + 1 / 2 ^ 50) 12 4 (1 / 2 ^ 52) (1 / 2 ^ 42) L (1 / 2 ^ 64)
    (1 / 2 ^ 12) hd hD (by norm_num) hCh hCl hl.1 hel hlb htop hM
    (by simp only [polyT, polyGrow, show (10 : UInt64).toNat = 10 from rfl]; norm_num)
    (by simp only [polyT, polyEps, polyLow, show (10 : UInt64).toNat = 10 from rfl]; norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨h1, h2, ?_, h4⟩
  have hh : horner (cDD mainTable 0) 10 L vd 9 = TgammaApprox.mainPoly vd := horner_main vd
  rw [show (10 : UInt64).toNat = 10 from rfl, show 10 - 1 = 9 from rfl, hh] at h3
  refine h3.trans ?_
  simp only [polyT, polyEps, polyLow]
  norm_num

#print axioms main_poly

end Library.Numerics.Float64.Tgamma.TgammaMainPoly
