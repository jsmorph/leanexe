import Library.Numerics.Float64.Lgamma.LgammaAccWin
import Library.Numerics.Float64.Lgamma.LgammaLogdOne
import Library.Numerics.Float64.Tgamma.TgammaAccPre

/-!
The windows of `Lgamma.accurate` about 1, 2, and 3, where the code multiplies the polynomial at
offset 0 of `accurateTable`, `log Γ (1 + t)/t`, by `t = x - c` (`small_val`) and adds logarithms.
At a positive argument the windows about 1 and 2 contain the zeros of `log Γ`, so their theorems
state the error relative to the target (`RelSpec`): about 1 the product is relative by itself
(`LgammaAccRange.small_range`), and about 2 the bound `|log Γ (2 + t)| ≥ 0.32 |t|` follows from the
convexity of `log Γ` and `log Γ (7/4) ≤ -0.08` (`two_lower`), while `LgammaLogdOne.acc_one` gives
the logarithm of `1 + t` within `2^-78` of itself where it is below `2^-12`.  At a negative
argument the windows return `log Γ (x + 1)` within an absolute error (`WinSpec`), which the
reflection uses.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccWinSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD LgammaLogAccKern LgammaAccLow
  LgammaAccAdd LgammaAccWin

set_option exponentiation.threshold 4096

/-- A triple within `ρ |T|` of `T`, with low parts relative to its high part. -/
def RelSpec (T ρ : ℝ) (r : Float × Float × Float) : Prop :=
  Finite r.1.toBits ∧ Finite r.2.1.toBits ∧ Finite r.2.2.toBits ∧
    |value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits - T| ≤ ρ * |T| ∧
    |value r.1.toBits| ≤ 4 ∧ |value r.2.1.toBits| ≤ |value r.1.toBits| / 2 ^ 20 ∧
    |value r.2.2.toBits| ≤ |value r.1.toBits| / 2 ^ 60

set_option maxHeartbeats 2000000 in
/-- **The product of the polynomial about 1** with `t`, within `|t|/2^69` of `log Γ (1 + t)`. -/
theorem small_val (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hAP : LgammaApprox.AccPolyFact) (t : Float)
    (ht : Finite t.toBits) (hT : |value t.toBits| ≤ 1 / 4)
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 0 34 t 0.0 = (p0, p1))
    (m0 m1 : Float) (hM : mulDDD t p0 p1 = (m0, m1)) :
    Finite m0.toBits ∧ Finite m1.toBits ∧
      |value m0.toBits + value m1.toBits - GammaBasic.lgamma (1 + value t.toBits)| ≤
        |value t.toBits| / 2 ^ 69 + 1 / 2 ^ 1072 ∧
      |value m1.toBits| ≤ |value t.toBits| / 2 ^ 42 + 1 / 2 ^ 1071 ∧
      |value m0.toBits| ≤ |value t.toBits| + 1 / 2 ^ 1075 ∧
      |value t.toBits| * (37 / 100) ≤ |GammaBasic.lgamma (1 + value t.toBits)| ∧
      |GammaBasic.lgamma (1 + value t.toBits)| ≤ |value t.toBits| * (83 / 100) := by
  set vt := value t.toBits with hvt
  obtain ⟨p0f, p1f, hpe, hp1, hpm⟩ := LgammaAccPoly.acc_gen hF Lgamma.accurateTable 0 34 (1 / 4)
    (95 / 100) (83 / 100) (1 / 2 ^ 54) (1 / 2 ^ 43) (1 / 2 ^ 42) (1 / 2 ^ 89)
    LgammaAccPoly.small_ok 0 34 rfl rfl (by norm_num) t ht (by push_cast; linarith)
  push_cast at hpe hp1 hpm
  rw [hP] at p0f p1f hpe hp1
  dsimp only at p0f p1f hpe hp1
  set ev := PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 0 34) vt with hev
  obtain ⟨r1, r2⟩ := LgammaAccRange.small_range vt hT
  have hAP1 : |GammaBasic.lgamma (1 + vt) - vt * ev| ≤ 1 / 2 ^ 70 * |vt| := hAP.1 vt hT
  have hvt0 := abs_nonneg vt
  have hp0 : |value p0.toBits| ≤ 96 / 100 := by
    have := abs_sub_abs_le_abs_sub (value p0.toBits + value p1.toBits) ev
    have h2 := abs_sub_abs_le_abs_sub (value p0.toBits) (-value p1.toBits)
    rw [sub_neg_eq_add, abs_neg] at h2
    linarith [(by norm_num : (95 : ℝ) / 100 + 1 / 2 ^ 89 + 1 / 2 ^ 43 + 1 / 2 ^ 43 ≤ 96 / 100)]
  obtain ⟨m0f, m1f, hme, hm1, hm0⟩ := mulDDD_spec hF t p0 p1 ht p0f p1f (96 / 100 * |vt|)
    (|vt| / 2 ^ 43)
    (by rw [← hvt]; have := mul_le_mul_of_nonneg_right hp0 (abs_nonneg vt); linarith)
    (by rw [← hvt]; have := mul_le_mul_of_nonneg_right hp1 (abs_nonneg vt); linarith)
    (by linarith [(by norm_num : (96 : ℝ) / 100 * (1 / 4) ≤ 2 ^ 900)])
    (by linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 43 ≤ 2 ^ 900)])
  try rw [← hvt] at hme
  rw [hM] at m0f m1f hme hm1 hm0
  dsimp only at m0f m1f hme hm1 hm0
  have hev_abs : |vt * ev| = |vt| * |ev| := abs_mul _ _
  have hev1 : 38 / 100 ≤ |ev| := by rw [abs_of_neg (by linarith)]; linarith
  have hev2 : |ev| ≤ 82 / 100 := by rw [abs_of_neg (by linarith)]; linarith
  refine ⟨m0f, m1f, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : |vt * (value p0.toBits + value p1.toBits) - vt * ev| ≤ |vt| / 2 ^ 89 := by
      rw [← mul_sub, abs_mul]
      have := mul_le_mul_of_nonneg_left hpe hvt0
      linarith
    have h2 := abs_sub_le (value m0.toBits + value m1.toBits) (vt * (value p0.toBits + value p1.toBits))
      (vt * ev)
    have h3 := abs_sub_le (value m0.toBits + value m1.toBits) (vt * ev) (GammaBasic.lgamma (1 + vt))
    rw [abs_sub_comm (vt * ev) (GammaBasic.lgamma (1 + vt))] at h3
    linarith
  · linarith
  · linarith
  · have := abs_sub_abs_le_abs_sub (vt * ev) (GammaBasic.lgamma (1 + vt))
    rw [abs_sub_comm] at this
    have := mul_le_mul_of_nonneg_left hev1 hvt0
    linarith
  · have := abs_sub_abs_le_abs_sub (GammaBasic.lgamma (1 + vt)) (vt * ev)
    have := mul_le_mul_of_nonneg_left hev2 hvt0
    linarith

/-- `|log Γ (2 + t)| ≥ 0.32 |t|` for `|t| < 1/4`, from the convexity of `log Γ`. -/
theorem two_lower (hAP : LgammaApprox.AccPolyFact) (t : ℝ) (ht : |t| < 1 / 4) :
    |t| * (8 / 25) - |t| / 2 ^ 68 ≤ |GammaBasic.lgamma (2 + t)| := by
  have h74 : GammaBasic.lgamma (7 / 4) ≤ -(2 / 25) + 1 / 2 ^ 70 := by
    have hA : |GammaBasic.lgamma (3 / 2 + 1 / 4) -
        PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 68 30) (1 / 4)| ≤ 1 / 2 ^ 70 :=
      hAP.2 (1 / 4) (by norm_num)
    have := (LgammaAccRange.mid_range (1 / 4) (by norm_num)).2
    rw [show (3 / 2 + 1 / 4 : ℝ) = 7 / 4 by norm_num] at hA
    linarith [(abs_le.mp hA).2]
  have hc := Real.convexOn_log_Gamma
  have h2 : GammaBasic.lgamma 2 = 0 := GammaBasic.lgamma_two
  rcases lt_trichotomy t 0 with h | h | h
  · have := hc.secant_mono_aux1 (x := 7 / 4) (y := 2 + t) (z := 2) (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by norm_num)) (by linarith [abs_lt.mp ht]) (by linarith)
    simp only [Function.comp] at this
    change (2 - 7 / 4) * GammaBasic.lgamma (2 + t) ≤
      (2 - (2 + t)) * GammaBasic.lgamma (7 / 4) + (2 + t - 7 / 4) * GammaBasic.lgamma 2 at this
    rw [h2, mul_zero, add_zero] at this
    rw [abs_of_neg h, abs_of_neg (by nlinarith)]
    nlinarith
  · subst h; simp
  · have := hc.secant_mono_aux1 (x := 7 / 4) (y := 2) (z := 2 + t) (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by linarith)) (by norm_num) (by linarith)
    simp only [Function.comp] at this
    change (2 + t - 7 / 4) * GammaBasic.lgamma 2 ≤
      (2 + t - 2) * GammaBasic.lgamma (7 / 4) + (2 - 7 / 4) * GammaBasic.lgamma (2 + t) at this
    rw [h2, mul_zero] at this
    rw [abs_of_pos h, abs_of_pos (by nlinarith)]
    nlinarith

/-- A double other than the integer `k`, within `1/2` of it and at least `1/4` in magnitude, lies
at least `2^-54` from `k`. -/
theorem near_int (x : Float) (hx : Finite x.toBits) (k : ℤ) (hk : |value x.toBits - k| < 1 / 2)
    (hne : value x.toBits ≠ k) (hq : 1 / 4 ≤ |value x.toBits|) : 1 / 2 ^ 54 ≤ |value x.toBits - k| := by
  obtain ⟨z, hz⟩ := Library.Numerics.Float64.Tgamma.TgammaAccPre.grid54 x hx hq
  have hnint : ∀ n : ℤ, value x.toBits ≠ n := by
    intro n hn
    rw [hn] at hk hne
    have : |((n - k : ℤ) : ℝ)| < 1 / 2 := by push_cast; exact hk
    have h2 : n - k = 0 := by
      by_contra h0
      have := Int.one_le_abs h0
      have : (1 : ℝ) ≤ |((n - k : ℤ) : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast this
      linarith
    exact hne (by rw [show n = k by omega])
  have := Library.Numerics.Float64.Tgamma.TgammaAccPre.dist_int (value x.toBits) z hz hnint (-k)
  push_cast at this
  rwa [← sub_eq_add_neg] at this

/-- `|log (1 + s)| ≤ |s|/(1 - |s|)` for `|s| < 1`. -/
theorem log_one_add (s : ℝ) (hs : |s| ≤ 1 / 4) : |Real.log (1 + s)| ≤ 4 / 3 * |s| := by
  have hs' := abs_le.mp hs
  have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + s by linarith)
  have h2 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + s by linarith)
  have hne : 1 + s ≠ 0 := by linarith
  have h3 : 1 - (1 + s)⁻¹ = s / (1 + s) := by field_simp; ring
  rw [h3] at h2
  rcases le_total 0 s with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by
      have : 0 ≤ s / (1 + s) := div_nonneg h (by linarith)
      linarith)]
    linarith
  · rw [abs_of_nonpos h, abs_of_nonpos (by linarith)]
    have : s / (1 + s) ≥ 4 / 3 * s := by
      rw [ge_iff_le, le_div_iff₀ (by linarith)]; nlinarith
    linarith

/-! ### The window about 1 -/

set_option maxHeartbeats 2000000 in
/-- **The window about 1 at a positive argument**: `log Γ x = t P (t)` for `t = x - 1`. -/
theorem w1_pos (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hAP : LgammaApprox.AccPolyFact) (x : Float)
    (hx : Finite x.toBits) (h1 : 3 / 4 < value x.toBits) (h2 : value x.toBits < 5 / 4)
    (hx1 : value x.toBits ≠ 1)
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 0 34 (x - 1.0) 0.0 = (p0, p1))
    (m0 m1 : Float) (hM : mulDDD (x - 1.0) p0 p1 = (m0, m1)) :
    RelSpec (GammaBasic.lgamma (value x.toBits)) (1 / 2 ^ 66) (m0, m1, 0.0) := by
  obtain ⟨tf, tv, tD⟩ := win_sub x 1.0 1 hx c10.1 c10.2 (by norm_num) (by norm_num) (by linarith)
    (by linarith)
  obtain ⟨m0f, m1f, he, hm1, hm0, hlo, hhi⟩ := small_val hF hAP (x - 1.0) tf tD p0 p1 hP m0 m1 hM
  rw [tv, show 1 + (value x.toBits - 1) = value x.toBits by ring] at he hlo hhi
  rw [tv] at hm1 hm0 tD
  have ht := near_int x hx 1 (by push_cast; exact abs_lt.mpr ⟨by linarith, by linarith⟩)
    (by push_cast; exact hx1) (by rw [abs_of_pos (by linarith)]; linarith)
  push_cast at ht
  set t := value x.toBits - 1
  set T := GammaBasic.lgamma (value x.toBits)
  have htiny : (1 : ℝ) / 2 ^ 1071 ≤ |t| / 2 ^ 1000 := by
    have := div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 2 ^ 1000)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1071 ≤ 1 / 2 ^ 54 / 2 ^ 1000)]
  have herr : |value m0.toBits + value m1.toBits - T| ≤ |T| / 2 ^ 66 := by
    have : |t| / 2 ^ 69 + 1 / 2 ^ 1072 ≤ |T| / 2 ^ 66 := by
      have := div_le_div_of_nonneg_right hlo (by norm_num : (0 : ℝ) ≤ 2 ^ 66)
      linarith
    linarith
  have hm0' : |t| * (36 / 100) ≤ |value m0.toBits| := by
    have h3 := abs_sub_abs_le_abs_sub T (value m0.toBits + value m1.toBits)
    rw [abs_sub_comm] at h3
    have h4 := abs_add_le (value m0.toBits) (value m1.toBits)
    have : |T| / 2 ^ 66 ≤ |t| * (83 / 100) / 2 ^ 66 := div_le_div_of_nonneg_right hhi (by norm_num)
    linarith
  refine ⟨m0f, m1f, zero_finite, ?_, ?_, ?_, ?_⟩
  · dsimp only; rw [zero_value, add_zero, mul_comm, ← div_eq_mul_one_div]; exact herr
  · dsimp only; linarith [abs_le.mp tD]
  · dsimp only
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 42 ≤ 36 / 100 / 2 ^ 20 - 1 / 2 ^ 900)]
  · dsimp only; rw [zero_value, abs_zero]; positivity

set_option maxHeartbeats 2000000 in
/-- The window about 1 before its logarithm: `log Γ x` within `2^-70`. -/
theorem w1_abs (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hAP : LgammaApprox.AccPolyFact) (x : Float)
    (hx : Finite x.toBits) (h1 : 3 / 4 < value x.toBits) (h2 : value x.toBits < 5 / 4)
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 0 34 (x - 1.0) 0.0 = (p0, p1))
    (m0 m1 : Float) (hM : mulDDD (x - 1.0) p0 p1 = (m0, m1)) :
    WinSpec (GammaBasic.lgamma (value x.toBits)) (1 / 2 ^ 70) (1 / 2 ^ 43) 0 (m0, m1, 0.0) ∧
      |GammaBasic.lgamma (value x.toBits)| ≤ 1 / 4 := by
  obtain ⟨tf, tv, tD⟩ := win_sub x 1.0 1 hx c10.1 c10.2 (by norm_num) (by norm_num) (by linarith)
    (by linarith)
  obtain ⟨m0f, m1f, he, hm1, hm0, hlo, hhi⟩ := small_val hF hAP (x - 1.0) tf tD p0 p1 hP m0 m1 hM
  rw [tv, show 1 + (value x.toBits - 1) = value x.toBits by ring] at he hlo hhi
  rw [tv] at hm1 hm0 tD
  refine ⟨⟨m0f, m1f, zero_finite, ?_, ?_, ?_, ?_⟩, by linarith⟩
  · dsimp only; rw [zero_value, add_zero]
    linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 69 + 1 / 2 ^ 1072 ≤ 1 / 2 ^ 70)]
  · dsimp only; linarith
  · dsimp only; linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 42 + 1 / 2 ^ 1071 ≤ 1 / 2 ^ 43)]
  · dsimp only; rw [zero_value, abs_zero]

set_option maxHeartbeats 2000000 in
/-- **The window about 1 at a negative argument**: `log Γ (x + 1) = log Γ x + log x`. -/
theorem w1_neg (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 3 / 4 < value x.toBits) (h2 : value x.toBits < 5 / 4)
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 0 34 (x - 1.0) 0.0 = (p0, p1))
    (m0 m1 : Float) (hM : mulDDD (x - 1.0) p0 p1 = (m0, m1))
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H x = (lh, ll, lll))
    (a1 b1 : Float) (hS1 : sumDD m1 0.0 ll lll = (a1, b1))
    (h2' l2 : Float) (hP2 : twoSum m0 lh = (h2', l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    WinSpec (GammaBasic.lgamma (value x.toBits + 1)) (1 / 2 ^ 69) (1 / 2 ^ 42) (1 / 2 ^ 85)
      (h2', a3, b3) := by
  obtain ⟨hw, hG⟩ := w1_abs hF hAP x hx h1 h2 p0 p1 hP m0 m1 hM
  obtain ⟨f0, f1, f2, el, b0, b1', b2⟩ := log_val hF hLA x hx (by linarith) (by linarith) lh ll lll hT
  have hlx := log_one_add (value x.toBits - 1) (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [show 1 + (value x.toBits - 1) = value x.toBits by ring] at hlx
  have hw2 := win_add m0 m1 0.0 lh ll lll _ _ _ _ _ _ hw (by norm_num) (by norm_num)
    (by norm_num) f0 f1 f2 el (by norm_num) (by linarith) (by linarith) (by linarith)
    (by
      have := abs_add_le (GammaBasic.lgamma (value x.toBits)) (Real.log (value x.toBits))
      have : |value x.toBits - 1| ≤ 1 / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith) a1 b1 hS1 h2' l2 hP2 a3 b3 hS3
  rw [← rec1 _ (by linarith)] at hw2
  exact win_mono hw2 (by norm_num) (by norm_num) (by norm_num)

/-! ### The window about 2 -/

set_option maxHeartbeats 2000000 in
/-- The window about 2 at its first logarithm: `log Γ x = log Γ (x - 1) + log (x - 1)` within
`2^-69`. -/
theorem w2_abs (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 7 / 4 < value x.toBits) (h2 : value x.toBits < 9 / 4)
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 1.0) = (lh, ll, lll))
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 0 34 (x - 2.0) 0.0 = (p0, p1))
    (m0 m1 : Float) (hM : mulDDD (x - 2.0) p0 p1 = (m0, m1))
    (a1 b1 : Float) (hS1 : sumDD m1 0.0 ll lll = (a1, b1))
    (h2' l2 : Float) (hP2 : twoSum m0 lh = (h2', l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    WinSpec (GammaBasic.lgamma (value x.toBits)) (1 / 2 ^ 69) (1 / 2 ^ 42) (1 / 2 ^ 85)
      (h2', a3, b3) ∧ |GammaBasic.lgamma (value x.toBits)| ≤ 3 / 4 := by
  obtain ⟨tf, tv, tD⟩ := win_sub x 2.0 2 hx c20.1 c20.2 (by norm_num) (by norm_num) (by linarith)
    (by linarith)
  obtain ⟨m0f, m1f, he, hm1, hm0, hlo, hhi⟩ := small_val hF hAP (x - 2.0) tf tD p0 p1 hP m0 m1 hM
  rw [tv] at he hm1 hm0 hlo hhi tD
  rw [show 1 + (value x.toBits - 2) = value x.toBits - 1 by ring] at he hlo hhi
  obtain ⟨yf, yv⟩ := sub_int x 1.0 hx c10.1 1 (by rw [c10.2]; norm_num) le_rfl (by norm_num)
    (by push_cast; linarith) (by linarith)
  push_cast at yv
  obtain ⟨f0, f1, f2, el, b0, b1', b2⟩ := log_val hF hLA (x - 1.0) yf (by rw [yv]; linarith)
    (by rw [yv]; linarith) lh ll lll hT
  rw [yv] at el
  have hw : WinSpec (GammaBasic.lgamma (value x.toBits - 1)) (1 / 2 ^ 70) (1 / 2 ^ 43) 0
      (m0, m1, 0.0) := by
    refine ⟨m0f, m1f, zero_finite, ?_, ?_, ?_, ?_⟩
    · dsimp only; rw [zero_value, add_zero]
      linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 69 + 1 / 2 ^ 1072 ≤ 1 / 2 ^ 70)]
    · dsimp only; linarith
    · dsimp only; linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 42 + 1 / 2 ^ 1071 ≤ 1 / 2 ^ 43)]
    · dsimp only; rw [zero_value, abs_zero]
  have hlx := log_one_add (value x.toBits - 2) tD
  rw [show 1 + (value x.toBits - 2) = value x.toBits - 1 by ring] at hlx
  have hTb : |GammaBasic.lgamma (value x.toBits - 1) + Real.log (value x.toBits - 1)| ≤ 3 / 4 := by
    have := abs_add_le (GammaBasic.lgamma (value x.toBits - 1)) (Real.log (value x.toBits - 1))
    linarith
  have hw2 := win_add m0 m1 0.0 lh ll lll _ _ _ _ _ _ hw (by norm_num) (by norm_num)
    (by norm_num) f0 f1 f2 el (by norm_num) (by linarith) (by linarith) (by linarith)
    (by linarith) a1 b1 hS1 h2' l2 hP2 a3 b3 hS3
  have hr := rec1 (value x.toBits - 1) (by linarith)
  rw [sub_add_cancel] at hr
  rw [← hr] at hw2 hTb
  exact ⟨win_mono hw2 (by norm_num) (by norm_num) (by norm_num), hTb⟩

set_option maxHeartbeats 2000000 in
/-- **The window about 2 at a negative argument**: `log Γ (x + 1) = log Γ x + log x`. -/
theorem w2_neg (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 7 / 4 < value x.toBits) (h2 : value x.toBits < 9 / 4)
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 1.0) = (lh, ll, lll))
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 0 34 (x - 2.0) 0.0 = (p0, p1))
    (m0 m1 : Float) (hM : mulDDD (x - 2.0) p0 p1 = (m0, m1))
    (a1 b1 : Float) (hS1 : sumDD m1 0.0 ll lll = (a1, b1))
    (h2' l2 : Float) (hP2 : twoSum m0 lh = (h2', l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3))
    (mh ml mll : Float) (hM2 : Lgamma.asLogdAccurate Tgamma.logdTable H x = (mh, ml, mll))
    (a4 b4 : Float) (hS4 : sumDD a3 b3 ml mll = (a4, b4))
    (h5 l5 : Float) (hP5 : twoSum h2' mh = (h5, l5))
    (a6 b6 : Float) (hS6 : sumDD a4 b4 l5 0.0 = (a6, b6)) :
    WinSpec (GammaBasic.lgamma (value x.toBits + 1)) (1 / 2 ^ 68) (1 / 2 ^ 41) (1 / 2 ^ 84)
      (h5, a6, b6) := by
  obtain ⟨hw, hG⟩ := w2_abs hF hLA hAP x hx h1 h2 lh ll lll hT p0 p1 hP m0 m1 hM a1 b1 hS1 h2' l2
    hP2 a3 b3 hS3
  obtain ⟨f0, f1, f2, el, b0, b1', b2⟩ := log_val hF hLA x hx (by linarith) (by linarith) mh ml mll hM2
  have hlx := log_upper (value x.toBits) (by linarith)
  have hlx2 : 0 < Real.log (value x.toBits) := Real.log_pos (by linarith)
  have hw2 := win_add h2' a3 b3 mh ml mll _ _ _ _ _ _ hw (by norm_num) (by norm_num)
    (by norm_num) f0 f1 f2 el (by norm_num) (by linarith) (by linarith) (by linarith)
    (by have := abs_add_le (GammaBasic.lgamma (value x.toBits)) (Real.log (value x.toBits))
        rw [abs_of_pos hlx2] at this; linarith)
    a4 b4 hS4 h5 l5 hP5 a6 b6 hS6
  rw [← rec1 _ (by linarith)] at hw2
  exact win_mono hw2 (by norm_num) (by norm_num) (by norm_num)

set_option maxHeartbeats 8000000 in
/-- **The window about 2 at a positive argument**, relative: `log Γ x` within `2^-64` of itself. -/
theorem w2_pos (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 7 / 4 < value x.toBits) (h2 : value x.toBits < 9 / 4) (hx2 : value x.toBits ≠ 2)
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 1.0) = (lh, ll, lll))
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 0 34 (x - 2.0) 0.0 = (p0, p1))
    (m0 m1 : Float) (hM : mulDDD (x - 2.0) p0 p1 = (m0, m1))
    (a1 b1 : Float) (hS1 : sumDD m1 0.0 ll lll = (a1, b1))
    (h2' l2 : Float) (hP2 : twoSum m0 lh = (h2', l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    RelSpec (GammaBasic.lgamma (value x.toBits)) (1 / 2 ^ 64) (h2', a3, b3) := by
  obtain ⟨tf, tv, tD⟩ := win_sub x 2.0 2 hx c20.1 c20.2 (by norm_num) (by norm_num) (by linarith)
    (by linarith)
  obtain ⟨m0f, m1f, he, hm1, hm0, hlo, hhi⟩ := small_val hF hAP (x - 2.0) tf tD p0 p1 hP m0 m1 hM
  rw [tv] at he hm1 hm0 hlo hhi tD
  rw [show 1 + (value x.toBits - 2) = value x.toBits - 1 by ring] at he hlo hhi
  obtain ⟨yf, yv⟩ := sub_int x 1.0 hx c10.1 1 (by rw [c10.2]; norm_num) le_rfl (by norm_num)
    (by push_cast; linarith) (by linarith)
  push_cast at yv
  have ht := near_int x hx 2 (by push_cast; exact abs_lt.mpr ⟨by linarith, by linarith⟩)
    (by push_cast; exact hx2) (by rw [abs_of_pos (by linarith)]; linarith)
  push_cast at ht
  have hTl := two_lower hAP (value x.toBits - 2) (abs_lt.mpr ⟨by linarith, by linarith⟩)
  rw [show 2 + (value x.toBits - 2) = value x.toBits by ring] at hTl
  have hlx := log_one_add (value x.toBits - 2) tD
  rw [show 1 + (value x.toBits - 2) = value x.toBits - 1 by ring] at hlx
  have hr := rec1 (value x.toBits - 1) (by linarith)
  rw [sub_add_cancel] at hr
  set t := value x.toBits - 2 with htdef
  set T := GammaBasic.lgamma (value x.toBits)
  have ht0 : 0 ≤ |t| := abs_nonneg t
  -- the logarithm of `x - 1 = 1 + t`, relative to `t`
  have hlog : Finite lh.toBits ∧ Finite ll.toBits ∧ Finite lll.toBits ∧
      |value lh.toBits + value ll.toBits + value lll.toBits - Real.log (value x.toBits - 1)| ≤
        |t| / 2 ^ 75 ∧
      |value lh.toBits| ≤ 1 ∧ |value ll.toBits| ≤ |t| / 2 ^ 35 + 1 / 2 ^ 84 ∧
      |value lll.toBits| ≤ |t| / 2 ^ 80 := by
    by_cases hsmall : |Real.log (value x.toBits - 1)| ≤ 1 / 2 ^ 12
    · have hy1 : value (x - 1.0).toBits ≠ 1 := by
        rw [yv]; intro h; apply hx2; linarith
      obtain ⟨g0, g1, g2, ge, gl, gz⟩ := LgammaLogdOne.acc_one hF hLA (x - 1.0) yf
        (by rw [yv]; linarith) hy1 (by rw [yv]; exact hsmall)
      rw [hT] at g0 g1 g2 ge gl gz
      dsimp only at g0 g1 g2 ge gl gz
      rw [yv] at ge gl
      have hle : |Real.log (value x.toBits - 1)| / 2 ^ 78 ≤ |t| / 2 ^ 75 := by
        have := div_le_div_of_nonneg_right hlx (by norm_num : (0 : ℝ) ≤ 2 ^ 78)
        linarith
      refine ⟨g0, g1, g2, ge.trans hle, ?_, ?_, by rw [gz]; simp; positivity⟩
      · have h3 := abs_sub_abs_le_abs_sub (value lh.toBits + value ll.toBits + value lll.toBits)
          (Real.log (value x.toBits - 1))
        have h4 := abs_sub_abs_le_abs_sub (value lh.toBits) (-(value ll.toBits + value lll.toBits))
        rw [sub_neg_eq_add, abs_neg, ← add_assoc] at h4
        have h5 := abs_add_le (value ll.toBits) (value lll.toBits)
        have h6 : |value lll.toBits| = 0 := by rw [gz, abs_zero]
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 12 + 1 / 4 / 2 ^ 75 + 1 / 2 ^ 12 / 2 ^ 43 +
          1 / 2 ^ 84 ≤ 1)]
      · have := div_le_div_of_nonneg_right hlx (by norm_num : (0 : ℝ) ≤ 2 ^ 43)
        linarith
    · obtain ⟨g0, g1, g2, ge, gb0, gb1, gb2⟩ := log_val hF hLA (x - 1.0) yf (by rw [yv]; linarith)
        (by rw [yv]; linarith) lh ll lll hT
      rw [yv] at ge
      have htb : 3 / 4 / 2 ^ 12 ≤ |t| := by push_neg at hsmall; linarith
      refine ⟨g0, g1, g2, ?_, ?_, ?_, ?_⟩
      · linarith [(by norm_num : (1 : ℝ) / 2 ^ 88 ≤ 3 / 4 / 2 ^ 12 / 2 ^ 75),
          div_le_div_of_nonneg_right htb (by norm_num : (0 : ℝ) ≤ 2 ^ 75)]
      · have h3 := abs_sub_abs_le_abs_sub (value lh.toBits + value ll.toBits + value lll.toBits)
          (Real.log (value x.toBits - 1))
        have h4 := abs_sub_abs_le_abs_sub (value lh.toBits) (-(value ll.toBits + value lll.toBits))
        rw [sub_neg_eq_add, abs_neg, ← add_assoc] at h4
        have h5 := abs_add_le (value ll.toBits) (value lll.toBits)
        linarith [(by norm_num : (1 : ℝ) / 3 + 1 / 2 ^ 88 + 1 / 2 ^ 48 + 1 / 2 ^ 98 ≤ 1)]
      · linarith [(by norm_num : (1 : ℝ) / 2 ^ 48 ≤ 3 / 4 / 2 ^ 12 / 2 ^ 35),
          div_le_div_of_nonneg_right htb (by norm_num : (0 : ℝ) ≤ 2 ^ 35)]
      · linarith [(by norm_num : (1 : ℝ) / 2 ^ 98 ≤ 3 / 4 / 2 ^ 12 / 2 ^ 80),
          div_le_div_of_nonneg_right htb (by norm_num : (0 : ℝ) ≤ 2 ^ 80)]
  obtain ⟨g0, g1, g2, ge, gb0, gb1, gb2⟩ := hlog
  have htiny : (1 : ℝ) / 2 ^ 80 ≤ |t| / 2 ^ 26 := by
    have := div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 2 ^ 26)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 80 ≤ 1 / 2 ^ 54 / 2 ^ 26)]
  obtain ⟨f2, f3, f4, herr, hh2, ha3, hb3⟩ := addLog_spec m0 m1 0.0 lh ll lll m0f m1f zero_finite
    g0 g1 g2 2 (|t| / 2 ^ 34 + 1 / 2 ^ 83) (|t| / 2 ^ 80)
    (by linarith) (by norm_num) (by linarith) (by linarith [abs_le.mp tD])
    (by rw [zero_value, abs_zero]; linarith) (by linarith [abs_le.mp tD])
    a1 b1 hS1 h2' l2 hP2 a3 b3 hS3
  rw [zero_value, add_zero] at herr
  -- `|h2'| ≤ 2`
  have hh2b : |value h2'.toBits| ≤ 2 := by
    have := abs_add_le (value m0.toBits) (value lh.toBits)
    nlinarith [(by norm_num : ((1 : ℝ) / 4 + 1 / 2 ^ 1075 + 1) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 2)]
  have herr' : |value h2'.toBits + value a3.toBits + value b3.toBits - T| ≤ |t| / 2 ^ 68 := by
    have k : value h2'.toBits + value a3.toBits + value b3.toBits - T =
        (value h2'.toBits + value a3.toBits + value b3.toBits -
          (value m0.toBits + value m1.toBits +
            (value lh.toBits + value ll.toBits + value lll.toBits))) +
        (value m0.toBits + value m1.toBits - GammaBasic.lgamma (value x.toBits - 1)) +
        (value lh.toBits + value ll.toBits + value lll.toBits - Real.log (value x.toBits - 1)) := by
      rw [hr]; ring
    rw [k]
    have e1 := abs_add_le ((value h2'.toBits + value a3.toBits + value b3.toBits -
          (value m0.toBits + value m1.toBits +
            (value lh.toBits + value ll.toBits + value lll.toBits))) +
        (value m0.toBits + value m1.toBits - GammaBasic.lgamma (value x.toBits - 1)))
      (value lh.toBits + value ll.toBits + value lll.toBits - Real.log (value x.toBits - 1))
    have e2 := abs_add_le (value h2'.toBits + value a3.toBits + value b3.toBits -
          (value m0.toBits + value m1.toBits +
            (value lh.toBits + value ll.toBits + value lll.toBits)))
      (value m0.toBits + value m1.toBits - GammaBasic.lgamma (value x.toBits - 1))
    have h1072 : (1 : ℝ) / 2 ^ 1072 ≤ |t| / 2 ^ 1000 := by
      have := div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 2 ^ 1000)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1072 ≤ 1 / 2 ^ 54 / 2 ^ 1000)]
    have hA : (7 * (|t| / 2 ^ 80) + (|t| / 2 ^ 34 + 1 / 2 ^ 83) / 2 ^ 47 +
        |value h2'.toBits| / 2 ^ 100) / 2 ^ 53 + 1 / 2 ^ 1100 ≤ |t| / 2 ^ 90 := by
      have h3 : |value h2'.toBits| / 2 ^ 100 ≤ 2 / 2 ^ 100 :=
        div_le_div_of_nonneg_right hh2b (by norm_num)
      have h4 : (2 : ℝ) / 2 ^ 100 ≤ |t| / 2 ^ 45 := by
        have := div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 2 ^ 45)
        linarith [(by norm_num : (2 : ℝ) / 2 ^ 100 ≤ 1 / 2 ^ 54 / 2 ^ 45)]
      have h5 : (1 : ℝ) / 2 ^ 83 / 2 ^ 47 ≤ |t| / 2 ^ 70 := by
        have := div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 2 ^ 70)
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 83 / 2 ^ 47 ≤ 1 / 2 ^ 54 / 2 ^ 70)]
      have h6 : (1 : ℝ) / 2 ^ 1100 ≤ |t| / 2 ^ 1000 := by
        have := div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 2 ^ 1000)
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 1100 ≤ 1 / 2 ^ 54 / 2 ^ 1000)]
      have h7 : 7 * (|t| / 2 ^ 80) + (|t| / 2 ^ 34 + 1 / 2 ^ 83) / 2 ^ 47 +
          |value h2'.toBits| / 2 ^ 100 ≤ |t| / 2 ^ 37 := by
        linarith
      have h8 := div_le_div_of_nonneg_right h7 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)
      linarith
    linarith
  -- the high part from below
  have hTl' : |t| * (31 / 100) ≤ |T| := by linarith
  have hh2lo : |t| * (30 / 100) ≤ |value h2'.toBits| := by
    have h3 := abs_sub_abs_le_abs_sub T (value h2'.toBits + value a3.toBits + value b3.toBits)
    rw [abs_sub_comm] at h3
    have h4 := abs_add_le (value h2'.toBits + value a3.toBits) (value b3.toBits)
    have h5 := abs_add_le (value h2'.toBits) (value a3.toBits)
    have h6 : |value a3.toBits| ≤ |t| / 2 ^ 33 + 1 / 2 ^ 82 + |value h2'.toBits| / 2 ^ 51 := by
      nlinarith
    have h7 : |value b3.toBits| ≤ |t| / 2 ^ 70 + |value h2'.toBits| / 2 ^ 100 := by
      have := div_le_div_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
      nlinarith
    have h8 : (1 : ℝ) / 2 ^ 82 ≤ |t| / 2 ^ 28 := by
      have := div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 2 ^ 28)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 82 ≤ 1 / 2 ^ 54 / 2 ^ 28)]
    nlinarith
  refine ⟨f2, f3, f4, ?_, ?_, ?_, ?_⟩
  · dsimp only
    have : |t| / 2 ^ 68 ≤ 1 / 2 ^ 64 * |T| := by
      have := mul_le_mul_of_nonneg_left hTl' (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 64)
      linarith
    linarith
  · dsimp only; linarith
  · dsimp only
    have h8 : (1 : ℝ) / 2 ^ 82 ≤ |t| / 2 ^ 28 := by
      have := div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 2 ^ 28)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 82 ≤ 1 / 2 ^ 54 / 2 ^ 28)]
    nlinarith
  · dsimp only
    have h6 : |value a3.toBits| ≤ |t| / 2 ^ 27 + |value h2'.toBits| / 2 ^ 51 := by
      have h8 : (1 : ℝ) / 2 ^ 82 ≤ |t| / 2 ^ 28 := by
        have := div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 2 ^ 28)
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 82 ≤ 1 / 2 ^ 54 / 2 ^ 28)]
      nlinarith
    have := div_le_div_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
    nlinarith

/-! ### The window about 3 -/

set_option maxHeartbeats 4000000 in
/-- **The window about 3 at a positive argument**:
`log Γ x = log Γ (x - 2) + log (x - 1) + log (x - 2)`, within `2^-68`. -/
theorem w3_pos (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 11 / 4 < value x.toBits) (h2 : value x.toBits < 13 / 4)
    (bh bl bll : Float) (hTb : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 2.0) = (bh, bl, bll))
    (ah al all : Float) (hTa : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 1.0) = (ah, al, all))
    (s1 t1 : Float) (hS1 : sumDD al all bl bll = (s1, t1))
    (s0 u : Float) (hP0 : fastTwoSum ah bh = (s0, u))
    (s1' s2 : Float) (hS2 : sumDD s1 t1 u 0.0 = (s1', s2))
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 0 34 (x - 3.0) 0.0 = (p0, p1))
    (m0 m1 : Float) (hM : mulDDD (x - 3.0) p0 p1 = (m0, m1))
    (a1 b1 : Float) (hS3 : sumDD m1 0.0 s1' s2 = (a1, b1))
    (h2' l2 : Float) (hP2 : twoSum m0 s0 = (h2', l2))
    (a3 b3 : Float) (hS4 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    WinSpec (GammaBasic.lgamma (value x.toBits)) (1 / 2 ^ 68) (1 / 2 ^ 42) (1 / 2 ^ 84)
      (h2', a3, b3) ∧ |GammaBasic.lgamma (value x.toBits)| ≤ 3 / 2 := by
  obtain ⟨tf, tv, tD⟩ := win_sub x 3.0 3 hx c30.1 c30.2 (by norm_num) (by norm_num) (by linarith)
    (by linarith)
  obtain ⟨m0f, m1f, he, hm1, hm0, hlo, hhi⟩ := small_val hF hAP (x - 3.0) tf tD p0 p1 hP m0 m1 hM
  rw [tv] at he hm1 hm0 hlo hhi tD
  rw [show 1 + (value x.toBits - 3) = value x.toBits - 2 by ring] at he hlo hhi
  obtain ⟨af, av⟩ := sub_int x 1.0 hx c10.1 1 (by rw [c10.2]; norm_num) le_rfl (by norm_num)
    (by push_cast; linarith) (by linarith)
  obtain ⟨bf, bv⟩ := sub_int x 2.0 hx c20.1 2 (by rw [c20.2]; norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by linarith)
  push_cast at av bv
  have hlb := log_one_add (value x.toBits - 3) tD
  rw [show 1 + (value x.toBits - 3) = value x.toBits - 2 by ring] at hlb
  have hla := Real.one_sub_inv_le_log_of_pos (show 0 < value x.toBits - 1 by linarith)
  have hla' : (3 : ℝ) / 7 ≤ 1 - (value x.toBits - 1)⁻¹ := by
    have : (value x.toBits - 1)⁻¹ ≤ 4 / 7 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hla2 := log_upper (value x.toBits - 1) (by linarith)
  obtain ⟨g0, g1, g2, eg, n0, n1, n2⟩ := log_sum hF hLA (x - 1.0) (x - 2.0) af bf
    (by rw [av]; linarith) (by rw [av]; linarith) (by rw [bv]; linarith) (by rw [bv]; linarith)
    (by rw [av, bv]; have := abs_le.mp hlb; exact abs_le.mpr ⟨by linarith, by linarith⟩)
    (by rw [av, bv, abs_of_pos (by linarith : 0 < Real.log (value x.toBits - 1))]
        have := abs_le.mp tD; linarith)
    bh bl bll hTb ah al all hTa s1 t1 hS1 s0 u hP0 s1' s2 hS2
  rw [av, bv] at eg
  have hw : WinSpec (GammaBasic.lgamma (value x.toBits - 2)) (1 / 2 ^ 70) (1 / 2 ^ 43) 0
      (m0, m1, 0.0) := by
    refine ⟨m0f, m1f, zero_finite, ?_, ?_, ?_, ?_⟩
    · dsimp only; rw [zero_value, add_zero]
      linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 69 + 1 / 2 ^ 1072 ≤ 1 / 2 ^ 70)]
    · dsimp only; linarith
    · dsimp only; linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 42 + 1 / 2 ^ 1071 ≤ 1 / 2 ^ 43)]
    · dsimp only; rw [zero_value, abs_zero]
  have hTsum : |GammaBasic.lgamma (value x.toBits - 2) + (Real.log (value x.toBits - 1) +
      Real.log (value x.toBits - 2))| ≤ 3 / 2 := by
    have := abs_le.mp hlb
    have := abs_le.mp tD
    have g1 := neg_abs_le (GammaBasic.lgamma (value x.toBits - 2))
    have g2 := le_abs_self (GammaBasic.lgamma (value x.toBits - 2))
    have g3 := neg_abs_le (Real.log (value x.toBits - 2))
    have g4 := le_abs_self (Real.log (value x.toBits - 2))
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hw2 := win_add m0 m1 0.0 s0 s1' s2 _ _ _ _ _ _ hw (by norm_num) (by norm_num)
    (by norm_num) g0 g1 g2 eg (by norm_num) n0 n1 n2 (by linarith) a1 b1 hS3 h2' l2 hP2 a3 b3 hS4
  have r1 := rec1 (value x.toBits - 2) (by linarith)
  have r2 := rec1 (value x.toBits - 1) (by linarith)
  rw [show value x.toBits - 2 + 1 = value x.toBits - 1 by ring] at r1
  rw [sub_add_cancel] at r2
  have hL : GammaBasic.lgamma (value x.toBits - 2) + (Real.log (value x.toBits - 1) +
      Real.log (value x.toBits - 2)) = GammaBasic.lgamma (value x.toBits) := by linarith
  rw [hL] at hw2 hTsum
  exact ⟨win_mono hw2 (by norm_num) (by norm_num) (by norm_num), hTsum⟩

set_option maxHeartbeats 4000000 in
/-- **The window about 3 at a negative argument**: `log Γ (x + 1) = log Γ x + log x`. -/
theorem w3_neg (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 11 / 4 < value x.toBits) (h2 : value x.toBits < 13 / 4)
    (bh bl bll : Float) (hTb : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 2.0) = (bh, bl, bll))
    (ah al all : Float) (hTa : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 1.0) = (ah, al, all))
    (s1 t1 : Float) (hS1 : sumDD al all bl bll = (s1, t1))
    (s0 u : Float) (hP0 : fastTwoSum ah bh = (s0, u))
    (s1' s2 : Float) (hS2 : sumDD s1 t1 u 0.0 = (s1', s2))
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 0 34 (x - 3.0) 0.0 = (p0, p1))
    (m0 m1 : Float) (hM : mulDDD (x - 3.0) p0 p1 = (m0, m1))
    (a1 b1 : Float) (hS3 : sumDD m1 0.0 s1' s2 = (a1, b1))
    (h2' l2 : Float) (hP2 : twoSum m0 s0 = (h2', l2))
    (a3 b3 : Float) (hS4 : sumDD a1 b1 l2 0.0 = (a3, b3))
    (mh ml mll : Float) (hM2 : Lgamma.asLogdAccurate Tgamma.logdTable H x = (mh, ml, mll))
    (a4 b4 : Float) (hS5 : sumDD a3 b3 ml mll = (a4, b4))
    (h5 l5 : Float) (hP5 : twoSum h2' mh = (h5, l5))
    (a6 b6 : Float) (hS6 : sumDD a4 b4 l5 0.0 = (a6, b6)) :
    WinSpec (GammaBasic.lgamma (value x.toBits + 1)) (1 / 2 ^ 67) (1 / 2 ^ 41) (1 / 2 ^ 83)
      (h5, a6, b6) := by
  obtain ⟨hw, hG⟩ := w3_pos hF hLA hAP x hx h1 h2 bh bl bll hTb ah al all hTa s1 t1 hS1 s0 u hP0
    s1' s2 hS2 p0 p1 hP m0 m1 hM a1 b1 hS3 h2' l2 hP2 a3 b3 hS4
  obtain ⟨f0, f1, f2, el, b0, b1', b2⟩ := log_val hF hLA x hx (by linarith) (by linarith) mh ml mll hM2
  have hlx := log_upper (value x.toBits) (by linarith)
  have hlx2 : 0 < Real.log (value x.toBits) := Real.log_pos (by linarith)
  have hw2 := win_add h2' a3 b3 mh ml mll _ _ _ _ _ _ hw (by norm_num) (by norm_num)
    (by norm_num) f0 f1 f2 el (by norm_num) (by linarith) (by linarith) (by linarith)
    (by have := abs_add_le (GammaBasic.lgamma (value x.toBits)) (Real.log (value x.toBits))
        rw [abs_of_pos hlx2] at this; linarith)
    a4 b4 hS5 h5 l5 hP5 a6 b6 hS6
  rw [← rec1 _ (by linarith)] at hw2
  exact win_mono hw2 (by norm_num) (by norm_num) (by norm_num)

#print axioms w1_pos
#print axioms w1_neg
#print axioms w2_abs
#print axioms w2_neg
#print axioms w2_pos
#print axioms w3_pos
#print axioms w3_neg

#print axioms small_val
#print axioms two_lower

end Library.Numerics.Float64.Lgamma.LgammaAccWinSmall
