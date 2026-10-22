import Library.Numerics.Float64.Lgamma.LgammaPolyFst
import Library.Numerics.Float64.Lgamma.LgammaFastTiny
import Library.Numerics.Float64.Tgamma.TgammaExpr
import Library.Numerics.Float64.Tgamma.TgammaWords
import Library.Numerics.Float64.Lgamma.LgammaApprox

/-!
The fast path of `Lgamma.lgammaWith` from `2 ^ -75` to `2 ^ -5` in magnitude: `-log |x|` from
`asLogd` plus `x P (x)`, with `P = LgammaApprox.smallPoly`.  The code evaluates the tail of degree 7
in plain double arithmetic (`lE`, bounded by `TgammaExpr`), adds `x` times it to the top
coefficient of the double-double Horner scheme of degree 3 (`LgammaPolyFst.polyFst_spec`),
multiplies by `x` (`mulDDD`), and adds `-log |x|` (`sumDD`).  `SmallFact` puts
`lgamma (1 + x) = lgamma x + log |x|` within `2 ^ -70 |x|` of `x P (x)`, and `|lgamma x| ≥ 3.38`,
so the error with `2 eps` lies far below `|lgamma x|/2 ^ 54` and `FastSpec` holds in its relative
form (`small_spec`).
-/

namespace Library.Numerics.Float64.Lgamma.LgammaFastSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaPoly Library.Numerics.Float64.Tgamma.TgammaPolyDDD Library.Numerics.Float64.Tgamma.TgammaExpr
  TgammaWords LgammaPolyFst LgammaWalk

set_option exponentiation.threshold 4096

def x2E : FE := .mul .var .var
def x4E : FE := .mul x2E x2E

def w (i : ℕ) : UInt64 := Lgamma.mainTable[i]!

/-- `a + x b`. -/
def lin (a b : UInt64) : FE := .add (.const a) (.mul .var (.const b))

/-- The tail `x ((q0 + x² q2) + x⁴ (q4 + x² q6))` of the code. -/
def lE : FE :=
  .mul .var (.add (.add (lin (w 389) (w 390)) (.mul x2E (lin (w 391) (w 392))))
    (.mul x4E (.add (lin (w 393) (w 394)) (.mul x2E (lin (w 395) (w 396))))))

theorem lE_ok : ok lE (1 / 32) = true := by decide +kernel

theorem lE_err : (bnd lE (1 / 32)).2 ≤ 1 / 2 ^ 55 := by decide +kernel

theorem lE_mag : (bnd lE (1 / 32)).1 ≤ 1 / 2 ^ 6 := by decide +kernel

theorem w_finite : ∀ k < 397, Wasm.IEEE64.isFinite Lgamma.mainTable[k]! = true := by
  decide +kernel

theorem hi_le : ∀ k < 4, PolyBound.qabs (PolyBound.ratOfWord Lgamma.mainTable[381 + 2 * k]!) ≤ 1 := by
  decide +kernel

theorem lo_le : ∀ k < 4,
    PolyBound.qabs (PolyBound.ratOfWord Lgamma.mainTable[381 + 2 * k + 1]!) ≤ 1 / 2 ^ 54 := by
  decide +kernel

theorem dom_ge : ∀ k < 3,
    3 / 8 ≤ PolyBound.qabs (PolyBound.ratOfWord Lgamma.mainTable[381 + 2 * k]!) := by
  decide +kernel

theorem top_ge : 1 / 4 ≤ PolyBound.qabs (PolyBound.ratOfWord Lgamma.mainTable[387]!) := by
  decide +kernel

theorem coef_sum : (∑ k ∈ Finset.range 4, PolyBound.qabs (PolyBound.ratOfWord
    Lgamma.mainTable[381 + 2 * k]! + PolyBound.ratOfWord Lgamma.mainTable[381 + 2 * k + 1]!)) ≤
    9 / 4 := by
  decide +kernel

theorem t381 : (381 : UInt64).toNat = 381 := rfl

theorem abs_rat_le (q B : ℚ) (h : PolyBound.qabs q ≤ B) : |(q : ℝ)| ≤ (B : ℝ) := by
  rw [← qabs_cast]
  exact_mod_cast h

/-- `evalR lE x = x Q(x)` with `Q` the coefficients `mainTable[389..396]`. -/
theorem lE_eval (x : ℝ) :
    evalR lE x = x * PolyBound.eval (Library.Numerics.Float64.Tgamma.TgammaApprox.coeffs Lgamma.mainTable 389 1 8) x := by
  rw [eval_coeffs]
  simp only [evalR, lE, lin, x2E, x4E, w, Library.Numerics.Float64.Tgamma.TgammaApprox.q, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd, zero_add, pow_zero, pow_one, mul_one]
  ring

/-- The exact Horner value of the small path is `smallPoly`. -/
theorem horner_small (x : ℝ) :
    horner (cDD Lgamma.mainTable 381) 4 (evalR lE x) x 3 = LgammaApprox.smallPoly x := by
  rw [show (3 : ℕ) = 4 - 1 from rfl, horner_eval _ 4 (by norm_num)]
  have hs : LgammaApprox.smallPoly x = PolyBound.eval (Library.Numerics.Float64.Tgamma.TgammaApprox.ddCoeffs Lgamma.mainTable 381 4 ++
      Library.Numerics.Float64.Tgamma.TgammaApprox.coeffs Lgamma.mainTable 389 1 8) x := rfl
  rw [hs, eval_append, eval_ddCoeffs, lE_eval]
  have hc : ∀ k ∈ Finset.range 4, cDD Lgamma.mainTable 381 k * x ^ k =
      ((Library.Numerics.Float64.Tgamma.TgammaApprox.q Lgamma.mainTable (381 + 2 * k) +
        Library.Numerics.Float64.Tgamma.TgammaApprox.q Lgamma.mainTable (381 + 2 * k + 1) : ℚ) : ℝ) * x ^ k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [cDD_rat Lgamma.mainTable 381 k (w_finite _ (by rw [t381]; omega))
      (w_finite _ (by rw [t381]; omega)), t381]
    simp [Library.Numerics.Float64.Tgamma.TgammaApprox.q]
  rw [Finset.sum_congr rfl hc]
  simp only [Library.Numerics.Float64.Tgamma.TgammaApprox.ddCoeffs, List.length_map, List.length_range]
  ring

/-- **The double-double polynomial of the small path** within `2 ^ -54` of `smallPoly`. -/
theorem small_poly (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (x : Float) (hx : Finite x.toBits)
    (hX : |value x.toBits| ≤ 1 / 32) :
    Finite (Lgamma.polyDDDFst Lgamma.mainTable 381 4 x (evalF lE x)).1.toBits ∧
      Finite (Lgamma.polyDDDFst Lgamma.mainTable 381 4 x (evalF lE x)).2.toBits ∧
      |value (Lgamma.polyDDDFst Lgamma.mainTable 381 4 x (evalF lE x)).1.toBits +
          value (Lgamma.polyDDDFst Lgamma.mainTable 381 4 x (evalF lE x)).2.toBits -
          LgammaApprox.smallPoly (value x.toBits)| ≤ 1 / 2 ^ 54 ∧
      |value (Lgamma.polyDDDFst Lgamma.mainTable 381 4 x (evalF lE x)).2.toBits| ≤ 1 / 2 ^ 5 ∧
      |LgammaApprox.smallPoly (value x.toBits)| ≤ 9 / 4 + 1 / 2 ^ 6 := by
  have hX' : |value x.toBits| ≤ ((1 / 32 : ℚ) : ℝ) := by push_cast; exact hX
  obtain ⟨hl, hLm⟩ := evalF_approx lE (1 / 32) x hx hX' lE_ok
  set vx := value x.toBits with hvx
  set L := evalR lE vx with hLdef
  have hel : |value (evalF lE x).toBits - L| ≤ 1 / 2 ^ 55 := by
    have h := hl.2
    have : ((bnd lE (1 / 32)).2 : ℝ) ≤ ((1 / 2 ^ 55 : ℚ) : ℝ) := by exact_mod_cast lE_err
    push_cast at this
    linarith
  have hLb : |L| ≤ 1 / 2 ^ 6 := by
    have : ((bnd lE (1 / 32)).1 : ℝ) ≤ ((1 / 2 ^ 6 : ℚ) : ℝ) := by exact_mod_cast lE_mag
    push_cast at this
    linarith
  have hlb : |value (evalF lE x).toBits| ≤ 1 / 2 ^ 6 + 1 / 2 ^ 55 := by
    have := abs_sub_abs_le_abs_sub (value (evalF lE x).toBits) L
    linarith
  have h381 : (381 : UInt64).toNat = 381 := rfl
  have hfh : ∀ k < (4 : UInt64).toNat,
      Finite (Float.ofBits Lgamma.mainTable[(381 : UInt64).toNat + 2 * k]!).toBits := by
    intro k hk
    rw [h381]
    exact ofBits_finite _ (w_finite _ (by simp at hk; omega))
  have hfl : ∀ k < (4 : UInt64).toNat,
      Finite (Float.ofBits Lgamma.mainTable[(381 : UInt64).toNat + 2 * k + 1]!).toBits := by
    intro k hk
    rw [h381]
    exact ofBits_finite _ (w_finite _ (by simp at hk; omega))
  have hCh : ∀ k < (4 : UInt64).toNat,
      |value (Float.ofBits Lgamma.mainTable[(381 : UInt64).toNat + 2 * k]!).toBits| ≤ 1 := by
    intro k hk
    have hk' : k < 4 := by simpa using hk
    rw [h381, ofBits_value _ (w_finite _ (by omega))]
    have := abs_rat_le _ _ (hi_le k hk')
    push_cast at this
    exact this
  have hCl : ∀ k < (4 : UInt64).toNat,
      |value (Float.ofBits Lgamma.mainTable[(381 : UInt64).toNat + 2 * k + 1]!).toBits| ≤
        1 / 2 ^ 54 := by
    intro k hk
    have hk' : k < 4 := by simpa using hk
    rw [h381, ofBits_value _ (w_finite _ (by omega))]
    have := abs_rat_le _ _ (lo_le k hk')
    push_cast at this
    exact this
  have htop : |value (evalF lE x).toBits| ≤
      |value (Float.ofBits Lgamma.mainTable[(381 : UInt64).toNat + 2 * ((4 : UInt64).toNat - 1)]!).toBits| := by
    rw [show (381 : UInt64).toNat + 2 * ((4 : UInt64).toNat - 1) = 387 from rfl,
      ofBits_value _ (w_finite 387 (by norm_num)), ← qabs_cast]
    have : ((1 / 4 : ℚ) : ℝ) ≤ ((PolyBound.qabs (PolyBound.ratOfWord Lgamma.mainTable[387]!) : ℚ) : ℝ) := by
      exact_mod_cast top_ge
    push_cast at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 6 + 1 / 2 ^ 55 ≤ 1 / 4)]
  have hM : ∀ m, m + 1 ≤ (4 : UInt64).toNat →
      |horner (cDD Lgamma.mainTable 381) (4 : UInt64).toNat L vx m| ≤ 9 / 4 + 1 / 2 ^ 6 := by
    intro m hm
    have h4 : (4 : UInt64).toNat = 4 := rfl
    rw [h4] at hm ⊢
    refine (horner_bound _ 4 L vx (hX.trans (by norm_num)) m hm).trans ?_
    have hs : (∑ k ∈ Finset.range 4, |cDD Lgamma.mainTable 381 k|) ≤ 9 / 4 := by
      have hc : ∀ k ∈ Finset.range 4, |cDD Lgamma.mainTable 381 k| =
          ((PolyBound.qabs (PolyBound.ratOfWord Lgamma.mainTable[381 + 2 * k]! +
            PolyBound.ratOfWord Lgamma.mainTable[381 + 2 * k + 1]!) : ℚ) : ℝ) := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [cDD_rat Lgamma.mainTable 381 k (w_finite _ (by rw [t381]; omega))
          (w_finite _ (by rw [t381]; omega)), t381, qabs_cast]
      rw [Finset.sum_congr rfl hc, ← Rat.cast_sum]
      calc _ ≤ ((9 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr coef_sum
        _ = 9 / 4 := by norm_num
    linarith
  have hdom : ∀ k, k + 2 ≤ (4 : UInt64).toNat →
      (9 / 4 + 1 / 2 ^ 6 + 1) * (1 / 32) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
        |value (Float.ofBits Lgamma.mainTable[(381 : UInt64).toNat + 2 * k]!).toBits| := by
    intro k hk
    have hk' : k < 3 := by simp at hk; omega
    rw [h381, ofBits_value _ (w_finite _ (by omega)), ← qabs_cast]
    have : ((3 / 8 : ℚ) : ℝ) ≤
        ((PolyBound.qabs (PolyBound.ratOfWord Lgamma.mainTable[381 + 2 * k]!) : ℚ) : ℝ) := by
      exact_mod_cast dom_ge k hk'
    push_cast at this
    linarith [(by norm_num : (9 / 4 + 1 / 2 ^ 6 + 1 : ℝ) * (1 / 32) * (1 + 1 / 2 ^ 53) +
      1 / 2 ^ 1075 ≤ 3 / 8)]
  obtain ⟨h1, h2, h3, h4⟩ := polyFst_spec hF Lgamma.mainTable 381 4 x (evalF lE x) (by decide)
    (by decide) hfh hfl (1 / 32) (9 / 4 + 1 / 2 ^ 6) 1 (1 / 2 ^ 54) (1 / 2 ^ 5) L (1 / 2 ^ 55)
    (1 / 2 ^ 6 + 1 / 2 ^ 55) hx hX (by norm_num) hCh hCl hl.1 hel hlb htop hM
    (by simp only [polyGrow, show (4 : UInt64).toNat = 4 from rfl]; norm_num)
    (by simp only [polyEps, polyLow, show (4 : UInt64).toNat = 4 from rfl]; norm_num)
    (by norm_num) (by norm_num) (by norm_num) hdom
  have hh : horner (cDD Lgamma.mainTable 381) 4 L vx 3 = LgammaApprox.smallPoly vx :=
    horner_small vx
  have hsb := hM 3 (by decide)
  rw [show (4 : UInt64).toNat = 4 from rfl, hh] at hsb
  refine ⟨h1, h2, ?_, h4, hsb⟩
  rw [show (4 : UInt64).toNat = 4 from rfl, show 4 - 1 = 3 from rfl, hh] at h3
  refine h3.trans ?_
  simp only [polyEps, polyLow]
  norm_num

#print axioms small_poly

/-- `|a| ≤ |a + b - c| + |c| + |b|`. -/
theorem abs_le_three (a b c : ℝ) : |a| ≤ |a + b - c| + |c| + |b| := by
  have h := abs_add_three (a + b - c) c (-b)
  rwa [show a + b - c + c + -b = a by ring, abs_neg] at h

/-- **The fast path from `2 ^ -75` to `2 ^ -5`.** -/
theorem small_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SmallFact) (x : Float) (hx : Finite x.toBits)
    (hlo : 1 / 2 ^ 75 ≤ |value x.toBits|) (hhi : |value x.toBits| < 1 / 32)
    (lh ll : Float) (h : Lgamma.asLogd Tgamma.logdTable x.abs = (lh, ll)) (sign : Float)
    (P M S : Float × Float) (hP : P = Lgamma.polyDDDFst Lgamma.mainTable 381 4 x (evalF lE x))
    (hM : M = Tgamma.mulDDD x P.1 P.2) (hSd : S = Tgamma.sumDD (-lh) (-ll) M.1 M.2) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (S.1, S.2, Float.ofBits 0x3B66AAD80C11872C, sign) := by
  have hv0 : 0 < |value x.toBits| := lt_of_lt_of_le (by positivity) hlo
  have hX : |value x.toBits| ≤ 1 / 32 := hhi.le
  -- `log |x|`
  obtain ⟨haf, hav⟩ := Library.Numerics.Float64.Sinh.SinhWords.abs_float x hx
  have hpos : 0 < value x.abs.toBits := by rw [hav]; exact hv0
  obtain ⟨hlf, hllf, herr, hllb⟩ := LgammaLogd.asLogd_spec hF hL x.abs haf hpos
  rw [h] at hlf hllf herr hllb
  dsimp only at hlf hllf herr hllb
  rw [hav] at herr
  obtain ⟨hnlf, hnlv⟩ := LgammaFastTiny.neg_float lh hlf
  obtain ⟨hnllf, hnllv⟩ := LgammaFastTiny.neg_float ll hllf
  have hl2a : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2b : Real.log 2 < 0.6932 := by have := Real.log_two_lt_d9; linarith
  have hg1 : Real.log |value x.toBits| < -3.4655 := by
    have h1 := Real.log_lt_log hv0 hhi
    rw [one_div, Real.log_inv, show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow] at h1
    push_cast at h1
    linarith
  have hg2 : -52 ≤ Real.log |value x.toBits| := by
    have h1 := Real.log_le_log (by positivity) hlo
    rw [one_div, Real.log_inv, Real.log_pow] at h1
    push_cast at h1
    linarith
  have hgabs : |Real.log (|value x.toBits|)| ≤ 52 := by rw [abs_le]; constructor <;> linarith
  have hab : |value lh.toBits| ≤ 54 := by
    have h1 := abs_le_three (value lh.toBits) (value ll.toBits) (Real.log |value x.toBits|)
    have h2 : |Real.log (|value x.toBits|)| / 2 ^ 78 ≤ 52 / 2 ^ 78 :=
      div_le_div_of_nonneg_right hgabs (by positivity)
    linarith
  have hbb : |value ll.toBits| ≤ 1 / 2 ^ 21 := by
    have h2 : |value lh.toBits| / 2 ^ 52 ≤ 54 / 2 ^ 52 :=
      div_le_div_of_nonneg_right hab (by positivity)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 22 + 54 / 2 ^ 52 ≤ 1 / 2 ^ 21)]
  -- the polynomial
  obtain ⟨hp1, hp2, hp3, hp4, hspb⟩ := small_poly hF x hx hX
  rw [← hP] at hp1 hp2 hp3 hp4
  have hp1b : |value P.1.toBits| ≤ 23 / 10 := by
    have h1 := abs_le_three (value P.1.toBits) (value P.2.toBits)
      (LgammaApprox.smallPoly (value x.toBits))
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 54 + (9 / 4 + 1 / 2 ^ 6) + 1 / 2 ^ 5 ≤ 23 / 10)]
  -- `x (fh + fl)`
  obtain ⟨hm1, hm2, hm3, hm4, hm5⟩ := Library.Numerics.Float64.Tgamma.TgammaDD.mulDDD_spec hF x P.1 P.2 hx hp1 hp2
    (23 / 10 * |value x.toBits|) (1 / 2 ^ 5 * |value x.toBits|)
    (mul_le_mul_of_nonneg_right hp1b (abs_nonneg _))
    (mul_le_mul_of_nonneg_right hp4 (abs_nonneg _)) (by linarith) (by linarith)
  rw [← hM] at hm1 hm2 hm3 hm4 hm5
  have hm1b : |value M.1.toBits| ≤ 1 / 4 := by linarith
  have hm2b : |value M.2.toBits| ≤ 1 / 2 ^ 9 := by linarith
  -- `-log |x| + x P (x)`
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := Library.Numerics.Float64.Tgamma.TgammaDD.sumDD_spec (-lh) (-ll) M.1 M.2 hnlf hnllf hm1 hm2
    (by rw [hnlv, abs_neg]; linarith) (by linarith) (1 / 2 ^ 21 + 1 / 2 ^ 9)
    (by rw [hnllv, abs_neg]; linarith) (by norm_num)
  rw [← hSd] at hs1 hs2 hs3 hs4 hs5
  rw [hnlv, hnllv] at hs3
  rw [hnlv] at hs5
  have hs1b : |value S.1.toBits| ≤ 56 := by
    have h1 := abs_add_le (-value lh.toBits) (value M.1.toBits)
    rw [abs_neg] at h1
    linarith
  -- `lgamma x = lgamma (1 + x) - log |x|`
  have hnp := GammaBasic.notPole_of_neg_one_lt (x := value x.toBits)
    (by linarith [neg_abs_le (value x.toBits)]) (abs_pos.mp hv0)
  have hsf := hS (value x.toBits) hX
  rw [add_comm 1 (value x.toBits), GammaBasic.lgamma_add_one hnp, GammaBasic.lgamma,
    ← Real.log_abs (value x.toBits)] at hsf
  have hvsp : |value x.toBits * LgammaApprox.smallPoly (value x.toBits)| ≤
      1 / 32 * (9 / 4 + 1 / 2 ^ 6) := by
    rw [abs_mul]; exact mul_le_mul hX hspb (abs_nonneg _) (by norm_num)
  have hvp : |value x.toBits * (value P.1.toBits + value P.2.toBits) -
      value x.toBits * LgammaApprox.smallPoly (value x.toBits)| ≤ 1 / 32 * (1 / 2 ^ 54) := by
    rw [← mul_sub, abs_mul]; exact mul_le_mul hX hp3 (abs_nonneg _) (by norm_num)
  -- the error bound
  have hcw : Wasm.IEEE64.isFinite 0x3B66AAD80C11872C = true := by decide
  have hcf : Finite (Float.ofBits 0x3B66AAD80C11872C).toBits := Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ hcw
  have hcq : (1 / 2 ^ 73 : ℚ) ≤ PolyBound.ratOfWord 0x3B66AAD80C11872C ∧
      PolyBound.ratOfWord 0x3B66AAD80C11872C ≤ 1 / 2 ^ 72 := by decide +kernel
  have hcv : value (Float.ofBits 0x3B66AAD80C11872C).toBits =
      (PolyBound.ratOfWord 0x3B66AAD80C11872C : ℝ) := Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ hcw
  have hc1 : (1 / 2 ^ 73 : ℝ) ≤ value (Float.ofBits 0x3B66AAD80C11872C).toBits := by
    have h := (Rat.cast_le (K := ℝ)).mpr hcq.1
    push_cast at h
    rw [hcv]; exact h
  have hc2 : value (Float.ofBits 0x3B66AAD80C11872C).toBits ≤ 1 / 2 ^ 72 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hcq.2
    push_cast at h
    rw [hcv]; exact h
  set L := Real.log (Real.Gamma (value x.toBits)) with hLdef
  have hL1 : 3 ≤ L := by
    linarith [(abs_le.mp hsf).1, (abs_le.mp hvsp).1]
  have hL2 : L ≤ 53 := by
    linarith [(abs_le.mp hsf).2, (abs_le.mp hvsp).2]
  have hE : |L - (value S.1.toBits + value S.2.toBits)| ≤ 1 / 2 ^ 57 := by
    rw [abs_le]
    constructor
    · linarith [(abs_le.mp hsf).1, (abs_le.mp hvp).2, (abs_le.mp hm3).2, (abs_le.mp hs3).2,
        (abs_le.mp herr).1]
    · linarith [(abs_le.mp hsf).2, (abs_le.mp hvp).1, (abs_le.mp hm3).1, (abs_le.mp hs3).1,
        (abs_le.mp herr).2]
  unfold FastSpec
  dsimp only
  rw [abs_of_pos (by linarith : (0 : ℝ) < L)]
  refine ⟨hs1, hs2, hcf, le_trans (by norm_num) hc1, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · linarith
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 3)]
  · linarith [(by norm_num : (53 : ℝ) ≤ 2 ^ 1020)]
  · linarith

#print axioms small_spec

end Library.Numerics.Float64.Lgamma.LgammaFastSmall
