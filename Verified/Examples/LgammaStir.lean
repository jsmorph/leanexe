import Verified.Examples.LgammaStirSeries

/-!
The fast path's Stirling series of `Lgamma.lgammaWith` from `border 19 = 8.29541` to `2 ^ 52`:
`(x - 1/2)(log x - 1)` from `asLogd`, with `log x - 1` and `x - 1/2` exact because both operands
lie on the spacing of the larger one (`grid_sub`), times the double-double product `mulDDD`, plus
the constant `c397 + c398` (`fastSum`) and the term `S (1/x²)/x` of `LgammaStirSeries.series_spec`
(`fastSum`).  The result lies within `2 ^ -67.4` of `stirFast x` relative, so with
`StirlingFact`'s `7 · 10^-20` it lies within `2 eps - |fh|/2^67` of `ln Γ x` for the code's
`eps = 4.5 · 10^-20 |fh|` (`stir_a`).
-/

namespace Verified.Examples.LgammaStir
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPolyDDD TgammaExpr TgammaWords
  LgammaPiecePoly LgammaFastSmall LgammaFastMid LgammaStirSeries

set_option exponentiation.threshold 4096

/-! ### Binades and exact differences -/

/-- A word of biased exponent `e` lies below `2 ^ (e - 1022)` in magnitude. -/
theorem binade_hi (w : UInt64) (e : ℕ) (he : Wasm.IEEE64.exponent w = e) (he2 : e ≤ 2046) :
    |value w| ≤ (2 : ℝ) ^ (e + 52) / 2 ^ 1074 := by
  have hexp := F64Order.exponent_abs w
  rw [he, show (2 : ℕ) ^ 52 = 4503599627370496 by norm_num] at hexp
  obtain ⟨hb2, hb2a⟩ := F64ExponentBounds.boundary_fields (e + 1) (by omega)
  have hw2 := F64PositiveSpacing.boundary_value (e + 1) (by omega) (by omega)
  have hu := F64Order.abs_value_mono w (F64ExponentBounds.boundary (e + 1)) (by
    rw [hb2a, UInt64.le_iff_toNat_le, hb2, show (2 : ℕ) ^ 52 = 4503599627370496 by norm_num]
    omega)
  rw [F64ExponentBounds.boundary, hw2,
    abs_of_pos (show (0 : ℝ) < 2 ^ (e + 1 + 51) / 2 ^ 1074 by positivity),
    show e + 1 + 51 = e + 52 by omega] at hu
  exact hu

/-- A normal word of biased exponent `e` lies at least `2 ^ (e - 1023)` in magnitude. -/
theorem binade_lo (w : UInt64) (e : ℕ) (he : Wasm.IEEE64.exponent w = e) (he1 : 1 ≤ e)
    (he2 : e ≤ 2046) : (2 : ℝ) ^ (e + 51) / 2 ^ 1074 ≤ |value w| := by
  have hexp := F64Order.exponent_abs w
  rw [he, show (2 : ℕ) ^ 52 = 4503599627370496 by norm_num] at hexp
  obtain ⟨hb1, hb1a⟩ := F64ExponentBounds.boundary_fields e (by omega)
  have hw1 := F64PositiveSpacing.boundary_value e he1 (by omega)
  have hl := F64Order.abs_value_mono (F64ExponentBounds.boundary e) w (by
    rw [hb1a, UInt64.le_iff_toNat_le, hb1, show (2 : ℕ) ^ 52 = 4503599627370496 by norm_num]
    omega)
  rw [F64ExponentBounds.boundary, hw1,
    abs_of_pos (show (0 : ℝ) < 2 ^ (e + 51) / 2 ^ 1074 by positivity)] at hl
  exact hl

/-- **The exact difference** `a - b` of a double `a` of biased exponent `e` and a double `b` on the
spacing `2 ^ (e - 1075)` of `a`, when `|a - b|` stays below `2 ^ (e - 1022)`. -/
theorem grid_sub (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (e : ℕ)
    (he : Wasm.IEEE64.exponent a.toBits = e) (he1 : 1 ≤ e) (he2 : e ≤ 2044) (mb : ℤ)
    (hmb : value b.toBits * 2 ^ 1074 = mb * 2 ^ (e - 1))
    (hab : |value a.toBits - value b.toBits| ≤ (2 : ℝ) ^ (e + 52) / 2 ^ 1074) :
    Finite (a - b).toBits ∧ value (a - b).toBits = value a.toBits - value b.toBits := by
  obtain ⟨ma, hma⟩ := value_grid a.toBits
  rw [he] at hma
  have hsum : (value a.toBits - value b.toBits) * 2 ^ 1074 = ((ma - mb : ℤ) : ℝ) * 2 ^ (e - 1) := by
    rw [sub_mul, hma, hmb]
    push_cast
    ring
  have hzb : |((ma - mb : ℤ) : ℝ)| ≤ 2 ^ 53 := by
    have hpos : (0 : ℝ) < 2 ^ (e - 1) := by positivity
    have h1 : |((ma - mb : ℤ) : ℝ)| * 2 ^ (e - 1) =
        |value a.toBits - value b.toBits| * 2 ^ 1074 := by
      rw [← abs_of_pos hpos, ← abs_mul, ← hsum, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
    have h2 : |value a.toBits - value b.toBits| * 2 ^ 1074 ≤ 2 ^ (e + 52) := by
      rw [le_div_iff₀ (by positivity)] at hab; exact hab
    have h3 : (2 : ℝ) ^ (e + 52) = 2 ^ 53 * 2 ^ (e - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [h3, ← h1] at h2
    exact le_of_mul_le_mul_right h2 hpos
  exact TgammaMainRed.sub_exact a b ha hb (ma - mb) (e - 1) (by omega) hsum hzb

/-- `x - c` is exact for a double `x` from 2 to `2 ^ 52` and `c = 2 ^ -k`, `k ≤ 1`, below `x`. -/
theorem sub_small_exact (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (k : ℕ)
    (hk : k ≤ 1) (hbv : value b.toBits = 1 / 2 ^ k) (h2 : 2 ≤ value a.toBits)
    (h52 : value a.toBits < 2 ^ 52) :
    Finite (a - b).toBits ∧ value (a - b).toBits = value a.toBits - value b.toBits := by
  have hpos : 0 < value a.toBits := by linarith
  set e := Wasm.IEEE64.exponent a.toBits with hedef
  have hel : e ≤ 2040 := F64Exact.exponent_le_of_value a.toBits
    (by rw [abs_of_pos hpos]; linarith [(by norm_num : (2 : ℝ) ^ 52 < 2 ^ 900)])
  have hhi := binade_hi a.toBits e rfl (by omega)
  rw [abs_of_pos hpos] at hhi
  have he1 : 1 ≤ e := by
    by_contra h0
    have h0' : e = 0 := by omega
    rw [h0'] at hhi
    norm_num at hhi
    linarith
  have hlo := binade_lo a.toBits e rfl he1 (by omega)
  rw [abs_of_pos hpos] at hlo
  have he74 : e + k ≤ 1075 := by
    by_contra hn
    have h1 : (2 : ℝ) ^ 1126 ≤ 2 ^ (e + 51) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2' : (2 : ℝ) ^ 1126 / 2 ^ 1074 ≤ 2 ^ (e + 51) / 2 ^ 1074 :=
      div_le_div_of_nonneg_right h1 (by positivity)
    have h3 : (2 : ℝ) ^ 1126 / 2 ^ 1074 = 2 ^ 52 := by norm_num
    linarith
  refine grid_sub a b ha hb e rfl he1 (by omega) (2 ^ (1075 - k - e)) ?_ ?_
  · rw [hbv]
    push_cast
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff (by positivity), ← pow_add, ← pow_add]
    congr 1
    omega
  · have hb0 : 0 < value b.toBits := by rw [hbv]; positivity
    have hb1 : value b.toBits ≤ 1 := by
      rw [hbv]; exact div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    rw [abs_of_pos (by linarith)]
    linarith

/-! ### The leaf from 8.29541 to `2 ^ 52` -/

theorem c5_bounds : (449 / 10 ^ 22 : ℚ) ≤ PolyBound.ratOfWord 0x3BEA90352E248A68 ∧
    PolyBound.ratOfWord 0x3BEA90352E248A68 ≤ 1 / 2 ^ 64 := by
  decide +kernel

theorem border19 : (829 / 100 : ℚ) ≤ LgammaApprox.border 19 := by decide +kernel

/-- `evalR sE t = t S(t)` with `S` the coefficients at word 401. -/
theorem sE_eval (t : ℝ) :
    evalR sE t = t * PolyBound.eval (LgammaApprox.coeffs Lgamma.mainTable 401 1 5) t := by
  rw [show LgammaApprox.coeffs Lgamma.mainTable 401 1 5 =
    TgammaApprox.coeffs Lgamma.mainTable 401 1 5 from rfl, eval_coeffs]
  simp only [evalR, sE, lin, wq, TgammaApprox.q, Finset.sum_range_succ, Finset.sum_range_zero,
    one_mul, add_zero, zero_add, pow_zero, pow_one, mul_one, Nat.reduceMul, Nat.reduceAdd]
  ring

/-- `stirFast` in the terms of the code. -/
theorem stirFast_eq (v : ℝ) :
    LgammaApprox.stirFast v = (v - 1 / 2) * (Real.log v - 1) +
      ((PolyBound.ratOfWord (wq 397) + PolyBound.ratOfWord (wq 398) : ℚ) : ℝ) +
      ((((PolyBound.ratOfWord (wq 399) + PolyBound.ratOfWord (wq 400) : ℚ)) : ℝ) +
        evalR sE ((1 / v) ^ 2)) * (1 / v) := by
  rw [LgammaApprox.stirFast, PolyBound.eval, sE_eval, one_div_pow]
  simp only [LgammaApprox.q]
  ring

set_option maxHeartbeats 2000000 in
/-- **The Stirling series of the fast path** from 8.29541 to `2 ^ 52`: the result within
`2 eps - |fh|/2^67` of `ln Γ x`, with `eps` the exact `4.5 · 10^-20 |fh|` less `|fh|/2^100`. -/
theorem stir_a (hF : FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hSF : LgammaApprox.StirlingFact) (ax : Float) (hax : Finite ax.toBits)
    (hb : (LgammaApprox.border 19 : ℝ) ≤ value ax.toBits) (h52 : value ax.toBits < 2 ^ 52)
    (L0 M N D T R : Float × Float)
    (hL0 : L0 = Lgamma.asLogd Tgamma.logdTable ax)
    (hM : M = mulDDD (ax - 0.5) (L0.1 - 1.0) L0.2)
    (hN : N = fastSum M.1 M.2 (entry Lgamma.mainTable 397) (entry Lgamma.mainTable 398))
    (hD : D = fastTwoSum (entry Lgamma.mainTable 399) (evalF sE ((1.0 / ax) * (1.0 / ax))))
    (hT : T = mulDD D.1 (D.2 + entry Lgamma.mainTable 400) (1.0 / ax)
      (Fma.fma (1.0 / ax) (-ax) 1.0 * (1.0 / ax)))
    (hR : R = fastSum N.1 N.2 T.1 T.2) :
    Finite R.1.toBits ∧ Finite R.2.toBits ∧ 8 ≤ value R.1.toBits ∧
      |value R.2.toBits| ≤ value R.1.toBits / 2 ^ 17 ∧ value R.1.toBits ≤ 2 ^ 58 ∧
      |GammaBasic.lgamma (value ax.toBits) - (value R.1.toBits + value R.2.toBits)| +
          value R.1.toBits / 2 ^ 67 ≤
        2 * (value R.1.toBits * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)) -
          value R.1.toBits / 2 ^ 100 := by
  set v := value ax.toBits with hvdef
  have hv1 : 829 / 100 ≤ v := by
    have := qcast_le border19; push_cast at this; linarith
  have hv0 : 0 < v := by linarith
  -- the logarithm
  have hl2a : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2b : Real.log 2 < 0.6932 := by have := Real.log_two_lt_d9; linarith
  have hg1 : (2.0793 : ℝ) ≤ Real.log v := by
    have h1 := Real.log_le_log (by norm_num) (show (8 : ℝ) ≤ v by linarith)
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h1
    push_cast at h1
    linarith
  have hg2 : Real.log v ≤ 36.05 := by
    have h1 := Real.log_le_log hv0 h52.le
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  obtain ⟨hlf, hllf, herr, hllb⟩ := LgammaLogd.asLogd_spec hF hL ax hax hv0
  rw [← hL0] at hlf hllf herr hllb
  set g := Real.log v with hgdef
  set lh := value L0.1.toBits with hlhdef
  set ll := value L0.2.toBits with hlldef
  have hgabs : |g| = g := abs_of_pos (by linarith)
  rw [hgabs] at herr
  have herr' : |lh + ll - g| ≤ 1 / 2 ^ 68 := by
    have : g / 2 ^ 78 ≤ 36.05 / 2 ^ 78 := div_le_div_of_nonneg_right hg2 (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 69 + 36.05 / 2 ^ 78 ≤ 1 / 2 ^ 68)]
  have hlh1 : |lh| ≤ 37 := by
    have h1 := abs_le_three lh ll g
    rw [hgabs] at h1
    linarith
  have hll : |ll| ≤ 1 / 2 ^ 21 := by
    have : |lh| / 2 ^ 52 ≤ 37 / 2 ^ 52 := div_le_div_of_nonneg_right hlh1 (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 22 + 37 / 2 ^ 52 ≤ 1 / 2 ^ 21)]
  have hlh2 : 2.07 ≤ lh := by
    have := abs_le.mp herr'; have := abs_le.mp hll; linarith
  have hlh3 : lh ≤ 36.1 := by
    have := abs_le.mp herr'; have := abs_le.mp hll; linarith
  -- `lh - 1` and `x - 1/2`, exact
  obtain ⟨hlmf, hlmv⟩ := sub_small_exact L0.1 1.0 hlf LgammaSpecial.one_finite 0 (by norm_num)
    (by rw [LgammaSpecial.one_value]; norm_num) (by linarith) (by linarith)
  rw [LgammaSpecial.one_value] at hlmv
  have hhalf : (0.5 : Float).toBits = 0x3FE0000000000000 := rfl
  have hhf : Finite (0.5 : Float).toBits := by
    rw [hhalf]; unfold CodeLib.IEEE64.Finite; decide
  have hhv : value (0.5 : Float).toBits = 1 / 2 ^ 1 := by
    rw [hhalf, word_value _ (1 / 2) (by decide +kernel)]; norm_num
  obtain ⟨hxmf, hxmv⟩ := sub_small_exact ax 0.5 hax hhf 1 le_rfl hhv (by linarith) h52
  rw [hhv, pow_one] at hxmv
  set B := v - 1 / 2 with hBdef
  have hB : 779 / 100 ≤ B := by rw [hBdef]; linarith
  have hB52 : B ≤ 2 ^ 52 := by rw [hBdef]; linarith
  have hBp : (0 : ℝ) < B := by linarith
  -- `M = (x - 1/2) (lh - 1 + ll)`
  have hH : |value (L0.1 - 1.0).toBits| * |value (ax - 0.5).toBits| ≤ 36 * B := by
    rw [hlmv, hxmv, abs_of_pos hBp]
    exact mul_le_mul_of_nonneg_right (by rw [abs_le]; constructor <;> linarith) hBp.le
  have hLw : |ll| * |value (ax - 0.5).toBits| ≤ 1 / 2 ^ 21 * B := by
    rw [hxmv, abs_of_pos hBp]
    exact mul_le_mul_of_nonneg_right hll hBp.le
  obtain ⟨hm1, hm2, hm3, hm4, hm5⟩ := mulDDD_spec hF (ax - 0.5) (L0.1 - 1.0) L0.2 hxmf hlmf hllf
    (36 * B) (1 / 2 ^ 21 * B) hH hLw (by linarith [(by norm_num : (36 : ℝ) * 2 ^ 52 ≤ 2 ^ 900)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 21 * 2 ^ 52 ≤ 2 ^ 900)])
  rw [← hM] at hm1 hm2 hm3 hm4 hm5
  rw [hxmv, hlmv] at hm3
  have hprod : B * 1.06 ≤ B * (lh - 1 + ll) := by
    apply mul_le_mul_of_nonneg_left _ hBp.le
    have := abs_le.mp hll; linarith
  -- constants against `B`
  have k70 : 1 / 2 ^ 1071 ≤ B / 2 ^ 70 := by
    have : (779 / 100 : ℝ) / 2 ^ 70 ≤ B / 2 ^ 70 := div_le_div_of_nonneg_right hB (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1071 ≤ 779 / 100 / 2 ^ 70)]
  have k50 : 1 / 2 ^ 50 ≤ B / 2 ^ 46 := by
    have : (779 / 100 : ℝ) / 2 ^ 46 ≤ B / 2 ^ 46 := div_le_div_of_nonneg_right hB (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 ≤ 779 / 100 / 2 ^ 46)]
  have k64 : 1 / 2 ^ 64 ≤ B / 2 ^ 64 / (779 / 100) := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    have : (1 : ℝ) / 2 ^ 64 * (779 / 100) ≤ B / 2 ^ 64 := by
      rw [show (1 : ℝ) / 2 ^ 64 * (779 / 100) = 779 / 100 / 2 ^ 64 by ring]
      exact div_le_div_of_nonneg_right hB (by norm_num)
    linarith
  have hM2 : |value M.2.toBits| ≤ B / 2 ^ 20 := by linarith
  have hM1lo : 105 / 100 * B ≤ value M.1.toBits := by
    have := abs_le.mp hm3
    have hm2' := abs_le.mp hM2
    linarith
  have hM1hi : value M.1.toBits ≤ 37 * B := by
    have := abs_le.mp hm5; linarith
  -- `N = M + c`
  obtain ⟨hw397, hw398⟩ : Wasm.IEEE64.isFinite (wq 397) = true ∧
      Wasm.IEEE64.isFinite (wq 398) = true := ⟨coef_ok.1 0 (by norm_num), coef_ok.1 1 (by norm_num)⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, h397a, h397b, h398⟩ := coef_ok
  have hc397a := qcast_le h397a
  have hc397b := qcast_le h397b
  have hc398 := abs_rat_le _ _ h398
  push_cast at hc397a hc397b hc398
  have he397 : entry Lgamma.mainTable 397 = Float.ofBits (wq 397) := rfl
  have he398 : entry Lgamma.mainTable 398 = Float.ofBits (wq 398) := rfl
  rw [he397, he398] at hN
  have hv397 := ofBits_value _ hw397
  have hv398 := ofBits_value _ hw398
  obtain ⟨hn1, hn2, hn3, hn4⟩ := fastSum_spec M.1 M.2 (Float.ofBits (wq 397)) (Float.ofBits (wq 398))
    hm1 hm2 (ofBits_finite _ hw397) (ofBits_finite _ hw398)
    (by rw [hv397, abs_of_pos (show (0 : ℝ) < ((PolyBound.ratOfWord (wq 397) : ℚ) : ℝ) by linarith),
      abs_of_pos (by linarith : (0 : ℝ) < value M.1.toBits)]; linarith)
    (by rw [abs_of_pos (by linarith : (0 : ℝ) < value M.1.toBits)]
        linarith [(by norm_num : (37 : ℝ) * 2 ^ 52 < 2 ^ 898)])
    (B / 2 ^ 20 + 1 / 2 ^ 57) (by rw [hv398]; linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 52 / 2 ^ 20 + 1 / 2 ^ 57 ≤ 2 ^ 800)])
  rw [← hN] at hn1 hn2 hn3 hn4
  rw [hv397, hv398] at hn3
  set n1 := value N.1.toBits with hn1def
  set n2 := value N.2.toBits with hn2def
  have hNs : |n1| ≤ |n1 + n2| + |n2| := by
    have := abs_sub (n1 + n2) n2
    rwa [add_sub_cancel_right] at this
  have hNm : |n1 + n2| ≤ 37 * B + B / 2 ^ 20 + 42 / 100 + 1 / 2 ^ 57 +
      (3 * (B / 2 ^ 20 + 1 / 2 ^ 57) + |n1| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by
    have h1 := abs_sub_abs_le_abs_sub (n1 + n2) (value M.1.toBits + value M.2.toBits +
      (((PolyBound.ratOfWord (wq 397) : ℚ) : ℝ) + ((PolyBound.ratOfWord (wq 398) : ℚ) : ℝ)))
    have h2 := abs_add_le (value M.1.toBits + value M.2.toBits)
      (((PolyBound.ratOfWord (wq 397) : ℚ) : ℝ) + ((PolyBound.ratOfWord (wq 398) : ℚ) : ℝ))
    have h3 := abs_add_le (value M.1.toBits) (value M.2.toBits)
    have h4 := abs_add_le ((PolyBound.ratOfWord (wq 397) : ℚ) : ℝ)
      ((PolyBound.ratOfWord (wq 398) : ℚ) : ℝ)
    rw [abs_of_pos (by linarith : (0 : ℝ) < value M.1.toBits),
      abs_of_pos (show (0 : ℝ) < ((PolyBound.ratOfWord (wq 397) : ℚ) : ℝ) by linarith)] at *
    linarith
  have hN1b : |n1| ≤ 38 * B := by
    have : 1 / 2 ^ 1073 ≤ B / 2 ^ 70 := by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1073 ≤ 1 / 2 ^ 1071)]
    linarith
  have hN2b : |n2| ≤ B / 2 ^ 19 := by
    have : |n1| / 2 ^ 51 ≤ 38 * B / 2 ^ 51 := div_le_div_of_nonneg_right hN1b (by norm_num)
    linarith
  have hN1lo : 104 / 100 * B ≤ n1 := by
    have := abs_le.mp hn3
    have := abs_le.mp hN2b
    have : |n1| / 2 ^ 52 ≤ 38 * B / 2 ^ 52 := div_le_div_of_nonneg_right hN1b (by norm_num)
    have := abs_le.mp hM2
    have := abs_le.mp hc398
    linarith
  -- the series
  obtain ⟨hT1, hT2, hTe, hT1b, hT2b⟩ := series_spec hF ax hax (by linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 52 ≤ 2 ^ 100)]) D T hD hT
  -- `R = N + T`
  obtain ⟨hr1, hr2, hr3, hr4⟩ := fastSum_spec N.1 N.2 T.1 T.2 hn1 hn2 hT1 hT2
    (by rw [abs_of_pos (by linarith : (0 : ℝ) < n1)]; linarith)
    (by linarith [abs_le.mp hN1b, (by norm_num : (38 : ℝ) * 2 ^ 52 < 2 ^ 898)])
    (B / 2 ^ 19 + 1 / 2 ^ 50) (by linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 52 / 2 ^ 19 + 1 / 2 ^ 50 ≤ 2 ^ 800)])
  rw [← hR] at hr1 hr2 hr3 hr4
  set r1 := value R.1.toBits with hr1def
  set r2 := value R.2.toBits with hr2def
  have hRs : |r1| ≤ |r1 + r2| + |r2| := by
    have := abs_sub (r1 + r2) r2
    rwa [add_sub_cancel_right] at this
  have hRm : |r1 + r2| ≤ 38 * B + B / 2 ^ 19 + 1 / 64 + 1 / 2 ^ 50 +
      (3 * (B / 2 ^ 19 + 1 / 2 ^ 50) + |r1| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by
    have h1 := abs_sub_abs_le_abs_sub (r1 + r2) (n1 + n2 + (value T.1.toBits + value T.2.toBits))
    have h2 := abs_add_le (n1 + n2) (value T.1.toBits + value T.2.toBits)
    have h3 := abs_add_le n1 n2
    have h4 := abs_add_le (value T.1.toBits) (value T.2.toBits)
    linarith
  have hR1b : |r1| ≤ 39 * B := by
    have : 1 / 2 ^ 1073 ≤ B / 2 ^ 70 := by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1073 ≤ 1 / 2 ^ 1071)]
    linarith
  have hR2b : |r2| ≤ B / 2 ^ 18 := by
    have : |r1| / 2 ^ 51 ≤ 39 * B / 2 ^ 51 := div_le_div_of_nonneg_right hR1b (by norm_num)
    linarith
  have hR1lo : 103 / 100 * B ≤ r1 := by
    have := abs_le.mp hr3; have := abs_le.mp hT1b; have := abs_le.mp hT2b
    have := abs_le.mp hN2b; have := abs_le.mp hR2b
    have : |r1| / 2 ^ 52 ≤ 39 * B / 2 ^ 52 := div_le_div_of_nonneg_right hR1b (by norm_num)
    linarith
  -- the error against `stirFast`
  set Tx := ((((PolyBound.ratOfWord (wq 399) + PolyBound.ratOfWord (wq 400) : ℚ)) : ℝ) +
    evalR sE ((1 / v) ^ 2)) * (1 / v) with hTxdef
  have hS := stirFast_eq v
  rw [← hTxdef, ← hBdef] at hS
  set c := ((PolyBound.ratOfWord (wq 397) + PolyBound.ratOfWord (wq 398) : ℚ) : ℝ) with hcdef
  have hc : c = ((PolyBound.ratOfWord (wq 397) : ℚ) : ℝ) + ((PolyBound.ratOfWord (wq 398) : ℚ) : ℝ) := by
    rw [hcdef]; push_cast; ring
  have hBg : |B * (lh - 1 + ll) - B * (g - 1)| ≤ B / 2 ^ 68 := by
    rw [show B * (lh - 1 + ll) - B * (g - 1) = B * (lh + ll - g) by ring, abs_mul, abs_of_pos hBp]
    calc B * |lh + ll - g| ≤ B * (1 / 2 ^ 68) := mul_le_mul_of_nonneg_left herr' hBp.le
      _ = B / 2 ^ 68 := by ring
  have hE : |LgammaApprox.stirFast v - (r1 + r2)| ≤ B / 2 ^ 67 + 1 / 2 ^ 64 := by
    rw [hS, hc]
    have e1 := abs_le.mp hm3
    have e2 := abs_le.mp hn3
    have e3 := abs_le.mp hr3
    have e4 := abs_le.mp hTe
    have e5 := abs_le.mp hBg
    have f1 : |n1| / 2 ^ 52 ≤ 38 * B / 2 ^ 52 := div_le_div_of_nonneg_right hN1b (by norm_num)
    have f2 : |r1| / 2 ^ 52 ≤ 39 * B / 2 ^ 52 := div_le_div_of_nonneg_right hR1b (by norm_num)
    rw [abs_le]
    constructor <;> linarith
  -- `StirlingFact`
  have hsf := hSF v (by linarith)
  set L := GammaBasic.lgamma v with hLdef
  have hTxb : |Tx| ≤ 1 / 32 := by
    have h1 := abs_sub_abs_le_abs_sub Tx (value T.1.toBits + value T.2.toBits)
    rw [abs_sub_comm] at h1
    have := abs_add_le (value T.1.toBits) (value T.2.toBits)
    linarith [(by norm_num : (1 : ℝ) / 64 + 1 / 2 ^ 50 + 1 / 2 ^ 65 ≤ 1 / 32)]
  have hSlo : B * 1.079 ≤ LgammaApprox.stirFast v := by
    rw [hS, hc]
    have : B * 1.079 ≤ B * (g - 1) := mul_le_mul_of_nonneg_left (by linarith) hBp.le
    have := abs_le.mp hTxb
    have := abs_le.mp hc398
    linarith
  have hc5 := qcast_le c5_bounds.1
  push_cast at hc5
  have hR1c : r1 * (449 / 10 ^ 22) ≤ r1 * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hc5 (by linarith)
  have hR2r : |r2| ≤ r1 / 2 ^ 17 := by
    have : B / 2 ^ 18 ≤ 103 / 100 * B / 2 ^ 17 := by linarith
    have : 103 / 100 * B / 2 ^ 17 ≤ r1 / 2 ^ 17 := div_le_div_of_nonneg_right hR1lo (by norm_num)
    linarith
  refine ⟨hr1, hr2, by linarith, hR2r, by linarith [abs_le.mp hR1b,
    (by norm_num : (39 : ℝ) * 2 ^ 52 ≤ 2 ^ 58)], ?_⟩
  -- the final comparison
  have hLpos : 0 ≤ L := by
    have h0 : 0 ≤ 7 / 10 ^ 20 * L := (abs_nonneg _).trans hsf
    linarith
  have hfin : |L - (r1 + r2)| ≤ 7 / 10 ^ 20 * L + (B / 2 ^ 67 + 1 / 2 ^ 64) := by
    have := abs_sub_le L (LgammaApprox.stirFast v) (r1 + r2)
    linarith
  have hLS : L ≤ LgammaApprox.stirFast v + 7 / 10 ^ 20 * L := by
    have := abs_le.mp hsf; linarith
  have hSR : LgammaApprox.stirFast v ≤ r1 * (1 + 1 / 2 ^ 16) := by
    have := abs_le.mp hE
    have := abs_le.mp hR2b
    have : B / 2 ^ 18 ≤ 103 / 100 * B / 2 ^ 17 := by linarith
    have : 103 / 100 * B / 2 ^ 17 ≤ r1 / 2 ^ 17 := div_le_div_of_nonneg_right hR1lo (by norm_num)
    have : B / 2 ^ 67 ≤ B / 2 ^ 19 := div_le_div_of_nonneg_left hBp.le (by norm_num) (by norm_num)
    have : B / 2 ^ 19 ≤ 103 / 100 * B / 2 ^ 18 := by linarith
    have : 103 / 100 * B / 2 ^ 18 ≤ r1 / 2 ^ 18 := div_le_div_of_nonneg_right hR1lo (by norm_num)
    have : 1 / 2 ^ 64 ≤ B / 2 ^ 60 := by
      have : (779 / 100 : ℝ) / 2 ^ 60 ≤ B / 2 ^ 60 := div_le_div_of_nonneg_right hB (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 64 ≤ 779 / 100 / 2 ^ 60)]
    linarith
  linarith

#print axioms grid_sub
#print axioms sub_small_exact
#print axioms stir_a

end Verified.Examples.LgammaStir
