import Verified.Examples.LgammaAccAdd
import Verified.Examples.LgammaAccRange

/-!
The windows of `Lgamma.accurate` about 0.5, 1.5, 2.5, and 3.5, where the code evaluates the
polynomial at offset 68 of `accurateTable`, `log Γ (3/2 + d)` (`LgammaAccPoly.mid_spec`), at
`d = x - c`, exact by Sterbenz's lemma, and adds or subtracts logarithms by the recurrence
`log Γ (y + 1) = log Γ y + log y`.  For a positive argument the window returns `log Γ x`, and for a
negative one `log Γ (x + 1)`, which the reflection uses.  `WinSpec T E B C` states that a triple
lies within `E` of `T` with a low part at most `B` and a last part at most `C`.  `mid_val` gives
the polynomial within `9/2^61 + 2^-70`, the error of the step whose `fastTwoSum` lacks the order
of its operands, `log_val` the logarithm of a double from `1/4` to 4, `log_sum` the sum of two
logarithms in the windows about 3 and 3.5, and `win_add` the addition of a logarithm triple
(`LgammaAccAdd.addLog_spec`).  Each window is within `9/2^61 + 2^-69` of its target.  The
theorems take the intermediate results of the code as variables with their equations.
-/

namespace Verified.Examples.LgammaAccWin
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD LgammaLogAccKern LgammaAccLow
  LgammaAccAdd

set_option exponentiation.threshold 4096

/-- A triple within `E` of `T` with parts bounded by 4, `B`, and `C`. -/
def WinSpec (T E B C : ℝ) (r : Float × Float × Float) : Prop :=
  Finite r.1.toBits ∧ Finite r.2.1.toBits ∧ Finite r.2.2.toBits ∧
    |value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits - T| ≤ E ∧
    |value r.1.toBits| ≤ 4 ∧ |value r.2.1.toBits| ≤ B ∧ |value r.2.2.toBits| ≤ C

/-- The error of a window from the polynomial about 3/2. -/
noncomputable def Emid : ℝ := 9 / 2 ^ 61 + 1 / 2 ^ 69

/-- Sterbenz's lemma for a `Float` subtraction. -/
theorem sub_exact (x c : Float) (hx : Finite x.toBits) (hc : Finite c.toBits)
    (h1 : |value x.toBits - value c.toBits| ≤ |value x.toBits|)
    (h2 : |value x.toBits - value c.toBits| ≤ |value c.toBits|)
    (h3 : |value c.toBits| < 2 ^ 1021) :
    Finite (x - c).toBits ∧ value (x - c).toBits = value x.toBits - value c.toBits := by
  rw [F64Bits.toBits_sub]
  exact F64Sterbenz.sub_exact _ _ hx hc h1 h2 h3

/-- A literal of the code. -/
theorem lit (f : Float) (w : UInt64) (q : ℚ) (hw : f.toBits = w)
    (hf : Wasm.IEEE64.isFinite w = true) (hq : PolyBound.ratOfWord w = q) :
    Finite f.toBits ∧ value f.toBits = (q : ℝ) := by
  rw [hw]
  exact ⟨hf, by rw [← PolyBound.ratOfWord_cast, hq]⟩

theorem c05 : Finite (0.5 : Float).toBits ∧ value (0.5 : Float).toBits = 1 / 2 := by
  have h := lit 0.5 0x3FE0000000000000 (1 / 2) rfl (by decide) (by decide +kernel)
  push_cast at h; exact h

theorem c10 : Finite (1.0 : Float).toBits ∧ value (1.0 : Float).toBits = 1 := by
  have h := lit 1.0 0x3FF0000000000000 1 rfl (by decide) (by decide +kernel)
  push_cast at h; exact h

theorem c15 : Finite (1.5 : Float).toBits ∧ value (1.5 : Float).toBits = 3 / 2 := by
  have h := lit 1.5 0x3FF8000000000000 (3 / 2) rfl (by decide) (by decide +kernel)
  push_cast at h; exact h

theorem c20 : Finite (2.0 : Float).toBits ∧ value (2.0 : Float).toBits = 2 := by
  have h := lit 2.0 0x4000000000000000 2 rfl (by decide) (by decide +kernel)
  push_cast at h; exact h

theorem c25 : Finite (2.5 : Float).toBits ∧ value (2.5 : Float).toBits = 5 / 2 := by
  have h := lit 2.5 0x4004000000000000 (5 / 2) rfl (by decide) (by decide +kernel)
  push_cast at h; exact h

theorem c30 : Finite (3.0 : Float).toBits ∧ value (3.0 : Float).toBits = 3 := by
  have h := lit 3.0 0x4008000000000000 3 rfl (by decide) (by decide +kernel)
  push_cast at h; exact h

theorem c35 : Finite (3.5 : Float).toBits ∧ value (3.5 : Float).toBits = 7 / 2 := by
  have h := lit 3.5 0x400C000000000000 (7 / 2) rfl (by decide) (by decide +kernel)
  push_cast at h; exact h

/-- `x - c` for a window about `c` from 1/2 to 7/2. -/
theorem win_sub (x c : Float) (cv : ℝ) (hx : Finite x.toBits) (hc : Finite c.toBits)
    (hcv : value c.toBits = cv) (hc1 : 1 / 2 ≤ cv) (hc2 : cv ≤ 4) (h1 : cv - 1 / 4 < value x.toBits)
    (h2 : value x.toBits < cv + 1 / 4) :
    Finite (x - c).toBits ∧ value (x - c).toBits = value x.toBits - cv ∧
      |value (x - c).toBits| ≤ 1 / 4 := by
  rw [← hcv] at h1 h2 hc1 hc2 ⊢
  have hd : |value x.toBits - value c.toBits| ≤ 1 / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨hf, hv⟩ := sub_exact x c hx hc
    (hd.trans (by rw [abs_of_pos (by linarith)]; linarith))
    (hd.trans (by rw [abs_of_pos (by linarith)]; linarith))
    (by rw [abs_of_pos (by linarith)]; linarith [(by norm_num : (4 : ℝ) < 2 ^ 1021)])
  exact ⟨hf, hv, by rw [hv]; exact hd⟩

theorem log_upper (y : ℝ) (hy : 0 < y) : Real.log y ≤ 6932 / 10000 + y / 2 - 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < y / 2 by positivity)
  rw [Real.log_div hy.ne' (by norm_num)] at h
  have := Real.log_two_lt_d9
  linarith

theorem log_lower (y : ℝ) (hy : 1 / 4 ≤ y) : -(1387 / 1000) ≤ Real.log y := by
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < 4 * y by positivity)
  rw [Real.log_mul (by norm_num) (by positivity),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
  have h1 : (0 : ℝ) ≤ 1 - ((2 : ℝ) ^ 2 * y)⁻¹ := by
    rw [sub_nonneg]; exact inv_le_one_of_one_le₀ (by nlinarith)
  have := Real.log_two_lt_d9
  push_cast at h
  linarith

/-- **The polynomial about 3/2** within `9/2^61 + 2^-70` of `log Γ (3/2 + d)`. -/
theorem mid_val (hF : FmaSpec.FmaNearest) (hAP : LgammaApprox.AccPolyFact) (d : Float)
    (hd : Finite d.toBits) (hD : |value d.toBits| ≤ 1 / 4) (p0 p1 : Float)
    (hP : Lgamma.polyDDDFst Lgamma.accurateTable 68 30 d 0.0 = (p0, p1)) :
    WinSpec (GammaBasic.lgamma (3 / 2 + value d.toBits)) (9 / 2 ^ 61 + 1 / 2 ^ 70) (1 / 2 ^ 40) 0
      (p0, p1, 0.0) ∧
      -(1 / 8 : ℝ) - 1 / 2 ^ 70 ≤ GammaBasic.lgamma (3 / 2 + value d.toBits) ∧
      GammaBasic.lgamma (3 / 2 + value d.toBits) ≤ -(2 / 25) + 1 / 2 ^ 70 := by
  obtain ⟨f0, f1, he, hl, hh⟩ := LgammaAccPoly.mid_spec hF d hd hD
  rw [hP] at f0 f1 he hl hh
  dsimp only at f0 f1 he hl hh
  have hA : |GammaBasic.lgamma (3 / 2 + value d.toBits) -
      PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 68 30) (value d.toBits)| ≤
      1 / 2 ^ 70 := hAP.2 (value d.toBits) hD
  obtain ⟨r1, r2⟩ := LgammaAccRange.mid_range (value d.toBits) hD
  have hA' := abs_le.mp hA
  refine ⟨⟨f0, f1, zero_finite, ?_, by linarith, hl, by rw [zero_value, abs_zero]⟩, by linarith,
    by linarith⟩
  rw [zero_value, add_zero]
  have := abs_sub_le (value p0.toBits + value p1.toBits)
    (PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 68 30) (value d.toBits))
    (GammaBasic.lgamma (3 / 2 + value d.toBits))
  rw [abs_sub_comm (PolyBound.eval _ _) (GammaBasic.lgamma _)] at this
  linarith

/-- **The logarithm** of a double from `1/4` to 4. -/
theorem log_val (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact) (y : Float)
    (hy : Finite y.toBits) (hlo : 1 / 4 ≤ value y.toBits) (hhi : value y.toBits ≤ 4)
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H y = (lh, ll, lll)) :
    Finite lh.toBits ∧ Finite ll.toBits ∧ Finite lll.toBits ∧
      |value lh.toBits + value ll.toBits + value lll.toBits - Real.log (value y.toBits)| ≤
        1 / 2 ^ 88 ∧
      |value lh.toBits| ≤ 2 ∧ |value ll.toBits| ≤ 1 / 2 ^ 48 ∧ |value lll.toBits| ≤ 1 / 2 ^ 98 := by
  obtain ⟨t1f, t2f, t3f, te, t2b, t3b⟩ :=
    LgammaLogdAcc.acc_abs hF hLA y hy (by linarith)
  rw [hT] at t1f t2f t3f te t2b t3b
  dsimp only at t1f t2f t3f te t2b t3b
  have hu := log_upper (value y.toBits) (by linarith)
  have hl := log_lower (value y.toBits) hlo
  have hlog : |Real.log (value y.toBits)| ≤ 17 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h3 : |value lh.toBits| ≤ 17 / 10 + 1 / 2 ^ 88 + |value ll.toBits| + |value lll.toBits| := by
    have h4 := abs_add_le (value lh.toBits + value ll.toBits + value lll.toBits -
      Real.log (value y.toBits)) (Real.log (value y.toBits) - (value ll.toBits + value lll.toBits))
    rw [show value lh.toBits + value ll.toBits + value lll.toBits - Real.log (value y.toBits) +
      (Real.log (value y.toBits) - (value ll.toBits + value lll.toBits)) = value lh.toBits by ring]
      at h4
    have h5 := abs_sub (Real.log (value y.toBits)) (value ll.toBits + value lll.toBits)
    have h6 := abs_add_le (value ll.toBits) (value lll.toBits)
    linarith
  have hlh : |value lh.toBits| ≤ 2 := by linarith
  refine ⟨t1f, t2f, t3f, te, hlh, ?_, ?_⟩
  · linarith [(by norm_num : (2 : ℝ) / 2 ^ 51 + 1 / 2 ^ 50 ≤ 1 / 2 ^ 48),
      div_le_div_of_nonneg_right hlh (by norm_num : (0 : ℝ) ≤ 2 ^ 51)]
  · linarith [(by norm_num : (2 : ℝ) / 2 ^ 100 + 1 / 2 ^ 100 ≤ 1 / 2 ^ 98),
      div_le_div_of_nonneg_right hlh (by norm_num : (0 : ℝ) ≤ 2 ^ 100)]

set_option maxHeartbeats 4000000 in
/-- **The addition of a logarithm triple** to a window's triple. -/
theorem win_add (fh fl fll lh ll lll : Float) (T E B0 C0 lam ε : ℝ)
    (hw : WinSpec T E B0 C0 (fh, fl, fll)) (hE : E ≤ 1 / 2 ^ 50) (hB0 : B0 ≤ 1 / 2 ^ 37)
    (hC0 : C0 ≤ 1 / 2 ^ 82)
    (hlh : Finite lh.toBits) (hll : Finite ll.toBits) (hlll : Finite lll.toBits)
    (hl : |value lh.toBits + value ll.toBits + value lll.toBits - lam| ≤ ε) (hε : ε ≤ 1 / 2 ^ 80)
    (hlhb : |value lh.toBits| ≤ 3) (hllb : |value ll.toBits| ≤ 1 / 2 ^ 46)
    (hlllb : |value lll.toBits| ≤ 1 / 2 ^ 90) (hT : |T + lam| ≤ 7 / 2)
    (a1 b1 : Float) (hS1 : sumDD fl fll ll lll = (a1, b1))
    (h2 l2 : Float) (hP2 : twoSum fh lh = (h2, l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    WinSpec (T + lam) (E + ε + 1 / 2 ^ 128) (B0 + 1 / 2 ^ 45) (C0 + 1 / 2 ^ 85) (h2, a3, b3) := by
  obtain ⟨hfh, hfl, hfll, he, hfhb, hflb, hfllb⟩ := hw
  dsimp only at hfh hfl hfll he hfhb hflb hfllb
  have hB00 : 0 ≤ B0 := le_trans (abs_nonneg _) hflb
  have hC00 : 0 ≤ C0 := le_trans (abs_nonneg _) hfllb
  obtain ⟨f2, f3, f4, herr, hh2, ha3, hb3⟩ := addLog_spec fh fl fll lh ll lll hfh hfl hfll hlh hll
    hlll 7 (B0 + 1 / 2 ^ 46) (C0 + 1 / 2 ^ 90) (by linarith) (by norm_num) (by linarith)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 37 + 1 / 2 ^ 46 ≤ 1)]) (by linarith)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 82 + 1 / 2 ^ 90 ≤ 1)]) a1 b1 hS1 h2 l2 hP2 a3 b3 hS3
  -- the high part
  have hsum : |value fh.toBits + value lh.toBits| ≤ 7 / 2 + 1 / 2 ^ 36 := by
    have k : value fh.toBits + value lh.toBits = (T + lam) +
        (value fh.toBits + value fl.toBits + value fll.toBits - T) +
        (value lh.toBits + value ll.toBits + value lll.toBits - lam) -
        (value fl.toBits + value fll.toBits + value ll.toBits + value lll.toBits) := by ring
    rw [k]
    have e1 := abs_add_le ((T + lam) + (value fh.toBits + value fl.toBits + value fll.toBits - T) +
      (value lh.toBits + value ll.toBits + value lll.toBits - lam))
      (-(value fl.toBits + value fll.toBits + value ll.toBits + value lll.toBits))
    have e2 := abs_add_le ((T + lam) + (value fh.toBits + value fl.toBits + value fll.toBits - T))
      (value lh.toBits + value ll.toBits + value lll.toBits - lam)
    have e3 := abs_add_le (T + lam) (value fh.toBits + value fl.toBits + value fll.toBits - T)
    have e4 := abs_add_le (value fl.toBits + value fll.toBits + value ll.toBits) (value lll.toBits)
    have e5 := abs_add_le (value fl.toBits + value fll.toBits) (value ll.toBits)
    have e6 := abs_add_le (value fl.toBits) (value fll.toBits)
    rw [abs_neg, ← sub_eq_add_neg] at e1
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 + 1 / 2 ^ 80 + 1 / 2 ^ 37 + 1 / 2 ^ 82 + 1 / 2 ^ 46 +
      1 / 2 ^ 90 ≤ 1 / 2 ^ 36)]
  have hh2' : |value h2.toBits| ≤ 4 := by
    nlinarith [(by norm_num : ((7 : ℝ) / 2 + 1 / 2 ^ 36) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 4)]
  refine ⟨f2, f3, f4, ?_, hh2', ?_, ?_⟩
  · dsimp only
    have k : value h2.toBits + value a3.toBits + value b3.toBits - (T + lam) =
        (value h2.toBits + value a3.toBits + value b3.toBits -
          (value fh.toBits + value fl.toBits + value fll.toBits +
            (value lh.toBits + value ll.toBits + value lll.toBits))) +
        (value fh.toBits + value fl.toBits + value fll.toBits - T) +
        (value lh.toBits + value ll.toBits + value lll.toBits - lam) := by ring
    rw [k]
    have e1 := abs_add_le (value h2.toBits + value a3.toBits + value b3.toBits -
          (value fh.toBits + value fl.toBits + value fll.toBits +
            (value lh.toBits + value ll.toBits + value lll.toBits)) +
        (value fh.toBits + value fl.toBits + value fll.toBits - T))
        (value lh.toBits + value ll.toBits + value lll.toBits - lam)
    have e2 := abs_add_le (value h2.toBits + value a3.toBits + value b3.toBits -
          (value fh.toBits + value fl.toBits + value fll.toBits +
            (value lh.toBits + value ll.toBits + value lll.toBits)))
        (value fh.toBits + value fl.toBits + value fll.toBits - T)
    have : (7 * (C0 + 1 / 2 ^ 90) + (B0 + 1 / 2 ^ 46) / 2 ^ 47 + |value h2.toBits| / 2 ^ 100) /
        2 ^ 53 + 1 / 2 ^ 1100 ≤ 1 / 2 ^ 128 := by
      have h4 := div_le_div_of_nonneg_right hh2' (by norm_num : (0 : ℝ) ≤ 2 ^ 100)
      have : 7 * (C0 + 1 / 2 ^ 90) + (B0 + 1 / 2 ^ 46) / 2 ^ 47 + |value h2.toBits| / 2 ^ 100 ≤
          7 * (1 / 2 ^ 82 + 1 / 2 ^ 90) + (1 / 2 ^ 37 + 1 / 2 ^ 46) / 2 ^ 47 + 4 / 2 ^ 100 := by
        linarith
      have h5 := div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 2 ^ 53)
      linarith [(by norm_num : (7 * (1 / 2 ^ 82 + 1 / 2 ^ 90) + (1 / 2 ^ 37 + 1 / 2 ^ 46) / 2 ^ 47 +
        4 / 2 ^ 100 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1100 ≤ 1 / 2 ^ 128)]
    linarith
  · dsimp only
    have h4 := div_le_div_of_nonneg_right hh2' (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
    nlinarith [(by norm_num : ((1 : ℝ) / 2 ^ 46 + 4 / 2 ^ 52) * (1 + 1 / 2 ^ 49) + 1 / 2 ^ 1070 +
      1 / 2 ^ 37 / 2 ^ 49 ≤ 1 / 2 ^ 45)]
  · dsimp only
    have h4 : |value a3.toBits| ≤ 1 / 2 ^ 36 := by
      have h5 := div_le_div_of_nonneg_right hh2' (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
      nlinarith [(by norm_num : ((1 : ℝ) / 2 ^ 37 + 1 / 2 ^ 46 + 4 / 2 ^ 52) * (1 + 1 / 2 ^ 49) +
        1 / 2 ^ 1070 ≤ 1 / 2 ^ 36)]
    have h5 := div_le_div_of_nonneg_right h4 (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
    nlinarith [(by norm_num : ((1 : ℝ) / 2 ^ 90 + (1 / 2 ^ 37 + 1 / 2 ^ 46) / 2 ^ 50) *
      (1 + 1 / 2 ^ 49) + 1 / 2 ^ 36 / 2 ^ 51 + 1 / 2 ^ 1070 + 1 / 2 ^ 82 / 2 ^ 49 ≤ 1 / 2 ^ 85)]

/-- The negation of a logarithm triple. -/
theorem neg_triple (lh ll lll : Float) (lam ε : ℝ) (hlh : Finite lh.toBits)
    (hll : Finite ll.toBits) (hlll : Finite lll.toBits)
    (hl : |value lh.toBits + value ll.toBits + value lll.toBits - lam| ≤ ε) :
    Finite (-lh).toBits ∧ Finite (-ll).toBits ∧ Finite (-lll).toBits ∧
      |value (-lh).toBits + value (-ll).toBits + value (-lll).toBits - -lam| ≤ ε ∧
      |value (-lh).toBits| = |value lh.toBits| ∧ |value (-ll).toBits| = |value ll.toBits| ∧
      |value (-lll).toBits| = |value lll.toBits| := by
  obtain ⟨f0, v0⟩ := neg_float lh hlh
  obtain ⟨f1, v1⟩ := neg_float ll hll
  obtain ⟨f2, v2⟩ := neg_float lll hlll
  refine ⟨f0, f1, f2, ?_, by rw [v0, abs_neg], by rw [v1, abs_neg], by rw [v2, abs_neg]⟩
  rw [v0, v1, v2, show -value lh.toBits + -value ll.toBits + -value lll.toBits - -lam =
    -(value lh.toBits + value ll.toBits + value lll.toBits - lam) by ring, abs_neg]
  exact hl

set_option maxHeartbeats 4000000 in
/-- **The sum of two logarithms** `log a + log b` of the windows about 3 and 3.5, with
`fastTwoSum` of the high parts for `|log b| ≤ |log a|`. -/
theorem log_sum (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact) (ya yb : Float)
    (hya : Finite ya.toBits) (hyb : Finite yb.toBits) (ha1 : 1 / 4 ≤ value ya.toBits)
    (ha2 : value ya.toBits ≤ 4) (hb1 : 1 / 4 ≤ value yb.toBits) (hb2 : value yb.toBits ≤ 4)
    (hsum : |Real.log (value ya.toBits) + Real.log (value yb.toBits)| ≤ 5 / 2)
    (hord : |Real.log (value yb.toBits)| + 1 / 2 ^ 40 ≤ |Real.log (value ya.toBits)|)
    (bh bl bll : Float) (hTb : Lgamma.asLogdAccurate Tgamma.logdTable H yb = (bh, bl, bll))
    (ah al all : Float) (hTa : Lgamma.asLogdAccurate Tgamma.logdTable H ya = (ah, al, all))
    (a1 b1 : Float) (hS1 : sumDD al all bl bll = (a1, b1))
    (h2 l2 : Float) (hP2 : fastTwoSum ah bh = (h2, l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    Finite h2.toBits ∧ Finite a3.toBits ∧ Finite b3.toBits ∧
      |value h2.toBits + value a3.toBits + value b3.toBits -
        (Real.log (value ya.toBits) + Real.log (value yb.toBits))| ≤ 1 / 2 ^ 86 ∧
      |value h2.toBits| ≤ 3 ∧ |value a3.toBits| ≤ 1 / 2 ^ 46 ∧ |value b3.toBits| ≤ 1 / 2 ^ 90 := by
  obtain ⟨fa0, fa1, fa2, ea, ba0, ba1, ba2⟩ := log_val hF hLA ya hya ha1 ha2 ah al all hTa
  obtain ⟨fb0, fb1, fb2, eb, bb0, bb1, bb2⟩ := log_val hF hLA yb hyb hb1 hb2 bh bl bll hTb
  have hord' : |value bh.toBits| ≤ |value ah.toBits| := by
    have h1 := abs_sub_abs_le_abs_sub (Real.log (value ya.toBits) -
      (value al.toBits + value all.toBits)) (value ah.toBits)
    have h2 := abs_sub_abs_le_abs_sub (value bh.toBits) (Real.log (value yb.toBits) -
      (value bl.toBits + value bll.toBits))
    rw [show Real.log (value ya.toBits) - (value al.toBits + value all.toBits) - value ah.toBits =
      -(value ah.toBits + value al.toBits + value all.toBits - Real.log (value ya.toBits)) by ring,
      abs_neg] at h1
    rw [show value bh.toBits - (Real.log (value yb.toBits) - (value bl.toBits + value bll.toBits)) =
      value bh.toBits + value bl.toBits + value bll.toBits - Real.log (value yb.toBits) by ring]
      at h2
    have h3 := abs_sub (Real.log (value ya.toBits)) (value al.toBits + value all.toBits)
    have h3' := abs_sub_abs_le_abs_sub (Real.log (value ya.toBits)) (value al.toBits + value all.toBits)
    have h4 := abs_sub (Real.log (value yb.toBits)) (value bl.toBits + value bll.toBits)
    have h5 := abs_add_le (value al.toBits) (value all.toBits)
    have h6 := abs_add_le (value bl.toBits) (value bll.toBits)
    linarith [(by norm_num : (2 : ℝ) / 2 ^ 88 + 2 / 2 ^ 48 + 2 / 2 ^ 98 ≤ 1 / 2 ^ 40)]
  obtain ⟨f2, f3, f4, herr, hh2, hha3, hhb3⟩ := addLog_fast ah al all bh bl bll fa0 fa1 fa2 fb0 fb1
    fb2 4 (2 / 2 ^ 48) (2 / 2 ^ 98) hord' (by linarith) (by norm_num) (by linarith) (by norm_num)
    (by linarith) (by norm_num) a1 b1 hS1 h2 l2 hP2 a3 b3 hS3
  have hsum' : |value ah.toBits + value bh.toBits| ≤ 5 / 2 + 1 / 2 ^ 46 := by
    have k : value ah.toBits + value bh.toBits =
        (Real.log (value ya.toBits) + Real.log (value yb.toBits)) +
        (value ah.toBits + value al.toBits + value all.toBits - Real.log (value ya.toBits)) +
        (value bh.toBits + value bl.toBits + value bll.toBits - Real.log (value yb.toBits)) -
        (value al.toBits + value all.toBits + value bl.toBits + value bll.toBits) := by ring
    rw [k]
    have e1 := abs_sub ((Real.log (value ya.toBits) + Real.log (value yb.toBits)) +
        (value ah.toBits + value al.toBits + value all.toBits - Real.log (value ya.toBits)) +
        (value bh.toBits + value bl.toBits + value bll.toBits - Real.log (value yb.toBits)))
      (value al.toBits + value all.toBits + value bl.toBits + value bll.toBits)
    have e2 := abs_add_le ((Real.log (value ya.toBits) + Real.log (value yb.toBits)) +
        (value ah.toBits + value al.toBits + value all.toBits - Real.log (value ya.toBits)))
      (value bh.toBits + value bl.toBits + value bll.toBits - Real.log (value yb.toBits))
    have e3 := abs_add_le (Real.log (value ya.toBits) + Real.log (value yb.toBits))
      (value ah.toBits + value al.toBits + value all.toBits - Real.log (value ya.toBits))
    have e4 := abs_add_le (value al.toBits + value all.toBits + value bl.toBits) (value bll.toBits)
    have e5 := abs_add_le (value al.toBits + value all.toBits) (value bl.toBits)
    have e6 := abs_add_le (value al.toBits) (value all.toBits)
    linarith [(by norm_num : (2 : ℝ) / 2 ^ 88 + 2 / 2 ^ 48 + 2 / 2 ^ 98 ≤ 1 / 2 ^ 46)]
  have hh2' : |value h2.toBits| ≤ 3 := by
    nlinarith [(by norm_num : ((5 : ℝ) / 2 + 1 / 2 ^ 46) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 3)]
  refine ⟨f2, f3, f4, ?_, hh2', ?_, ?_⟩
  · have k : value h2.toBits + value a3.toBits + value b3.toBits -
        (Real.log (value ya.toBits) + Real.log (value yb.toBits)) =
        (value h2.toBits + value a3.toBits + value b3.toBits -
          (value ah.toBits + value al.toBits + value all.toBits +
            (value bh.toBits + value bl.toBits + value bll.toBits))) +
        (value ah.toBits + value al.toBits + value all.toBits - Real.log (value ya.toBits)) +
        (value bh.toBits + value bl.toBits + value bll.toBits - Real.log (value yb.toBits)) := by
      ring
    rw [k]
    have e1 := abs_add_le ((value h2.toBits + value a3.toBits + value b3.toBits -
          (value ah.toBits + value al.toBits + value all.toBits +
            (value bh.toBits + value bl.toBits + value bll.toBits))) +
        (value ah.toBits + value al.toBits + value all.toBits - Real.log (value ya.toBits)))
      (value bh.toBits + value bl.toBits + value bll.toBits - Real.log (value yb.toBits))
    have e2 := abs_add_le (value h2.toBits + value a3.toBits + value b3.toBits -
          (value ah.toBits + value al.toBits + value all.toBits +
            (value bh.toBits + value bl.toBits + value bll.toBits)))
      (value ah.toBits + value al.toBits + value all.toBits - Real.log (value ya.toBits))
    have h4 := div_le_div_of_nonneg_right hh2' (by norm_num : (0 : ℝ) ≤ 2 ^ 100)
    have : (7 * (2 / 2 ^ 98) + 2 / 2 ^ 48 / 2 ^ 47 + |value h2.toBits| / 2 ^ 100) / 2 ^ 53 +
        1 / 2 ^ 1100 ≤ 1 / 2 ^ 140 := by
      have h5 : 7 * (2 / 2 ^ 98) + 2 / 2 ^ 48 / 2 ^ 47 + |value h2.toBits| / 2 ^ 100 ≤
          7 * (2 / 2 ^ 98) + 2 / 2 ^ 48 / 2 ^ 47 + 3 / 2 ^ 100 := by linarith
      have h6 := div_le_div_of_nonneg_right h5 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)
      linarith [(by norm_num : (7 * (2 / 2 ^ 98) + 2 / 2 ^ 48 / 2 ^ 47 + 3 / 2 ^ 100 : ℝ) / 2 ^ 53 +
        1 / 2 ^ 1100 ≤ 1 / 2 ^ 140)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 140 + 1 / 2 ^ 88 + 1 / 2 ^ 88 ≤ 1 / 2 ^ 86)]
  · have h4 := div_le_div_of_nonneg_right hh2' (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
    nlinarith [(by norm_num : ((2 : ℝ) / 2 ^ 48 + 3 / 2 ^ 52) * (1 + 1 / 2 ^ 49) + 1 / 2 ^ 1070 ≤
      1 / 2 ^ 46)]
  · have h4 : |value a3.toBits| ≤ 1 / 2 ^ 46 := by
      have h5 := div_le_div_of_nonneg_right hh2' (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
      nlinarith [(by norm_num : ((2 : ℝ) / 2 ^ 48 + 3 / 2 ^ 52) * (1 + 1 / 2 ^ 49) + 1 / 2 ^ 1070 ≤
        1 / 2 ^ 46)]
    have h5 := div_le_div_of_nonneg_right h4 (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
    nlinarith [(by norm_num : ((2 : ℝ) / 2 ^ 98 + 2 / 2 ^ 48 / 2 ^ 50) * (1 + 1 / 2 ^ 49) +
      1 / 2 ^ 46 / 2 ^ 51 + 1 / 2 ^ 1070 ≤ 1 / 2 ^ 90)]

theorem win_mono {T E B C E' B' C' : ℝ} {r : Float × Float × Float} (h : WinSpec T E B C r)
    (hE : E ≤ E') (hB : B ≤ B') (hC : C ≤ C') : WinSpec T E' B' C' r := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨a, b, c, d.trans hE, e, f.trans hB, g.trans hC⟩

theorem win_congr {T T' E B C : ℝ} {r : Float × Float × Float} (h : WinSpec T E B C r)
    (hT : T = T') : WinSpec T' E B C r := hT ▸ h

/-- `x - k` for `k` from 1 to 3 and `k ≤ x < 4`, exact on the binade of `x`. -/
theorem sub_int (x c : Float) (hx : Finite x.toBits) (hc : Finite c.toBits) (k : ℕ)
    (hcv : value c.toBits = k) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (h1 : (k : ℝ) ≤ value x.toBits)
    (h2 : value x.toBits < 4) :
    Finite (x - c).toBits ∧ value (x - c).toBits = value x.toBits - k := by
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  rcases lt_or_ge (value x.toBits) 2 with h | h
  · obtain ⟨f, v⟩ := TgammaAsym1.sub_exact_binade x c hx hc 0 (by norm_num)
      (by norm_num; linarith) (by norm_num; linarith) (by rw [hcv]; positivity)
      (by rw [hcv]; linarith) (k * 2 ^ 52) (by rw [hcv]; push_cast; ring)
    exact ⟨f, by rw [v, hcv]⟩
  · obtain ⟨f, v⟩ := TgammaAsym1.sub_exact_binade x c hx hc 1 (by norm_num)
      (by norm_num; linarith) (by norm_num; linarith) (by rw [hcv]; positivity)
      (by rw [hcv]; linarith) (k * 2 ^ 51) (by rw [hcv]; push_cast; ring)
    exact ⟨f, by rw [v, hcv]⟩

theorem rec1 (v : ℝ) (hv : 0 < v) : GammaBasic.lgamma (v + 1) = GammaBasic.lgamma v + Real.log v :=
  GammaBasic.lgamma_add_one (GammaBasic.notPole_of_neg_one_lt (by linarith) hv.ne')

/-! ### The window about 0.5 -/

/-- **The window about 0.5 at a negative argument**: `log Γ (x + 1)`. -/
theorem w05_neg (hF : FmaSpec.FmaNearest) (hAP : LgammaApprox.AccPolyFact) (x : Float)
    (hx : Finite x.toBits) (h1 : 1 / 4 < value x.toBits) (h2 : value x.toBits < 3 / 4)
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 68 30 (x - 0.5) 0.0 = (p0, p1)) :
    WinSpec (GammaBasic.lgamma (value x.toBits + 1)) Emid (1 / 2 ^ 40) 0 (p0, p1, 0.0) := by
  obtain ⟨df, dv, dD⟩ := win_sub x 0.5 (1 / 2) hx c05.1 c05.2 (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  obtain ⟨hw, -, -⟩ := mid_val hF hAP (x - 0.5) df dD p0 p1 hP
  rw [dv, show 3 / 2 + (value x.toBits - 1 / 2) = value x.toBits + 1 by ring] at hw
  exact win_mono hw (by unfold Emid; norm_num) le_rfl le_rfl

set_option maxHeartbeats 2000000 in
/-- **The window about 0.5 at a positive argument**: `log Γ x = log Γ (x + 1) - log x`. -/
theorem w05_pos (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 1 / 4 < value x.toBits) (h2 : value x.toBits < 3 / 4)
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 68 30 (x - 0.5) 0.0 = (p0, p1))
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H x = (lh, ll, lll))
    (a1 b1 : Float) (hS1 : sumDD p1 0.0 (-ll) (-lll) = (a1, b1))
    (h2' l2 : Float) (hP2 : twoSum p0 (-lh) = (h2', l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    WinSpec (GammaBasic.lgamma (value x.toBits)) Emid (1 / 2 ^ 39) (1 / 2 ^ 84) (h2', a3, b3) := by
  obtain ⟨df, dv, dD⟩ := win_sub x 0.5 (1 / 2) hx c05.1 c05.2 (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  obtain ⟨hw, hlo, hhi⟩ := mid_val hF hAP (x - 0.5) df dD p0 p1 hP
  rw [dv, show 3 / 2 + (value x.toBits - 1 / 2) = value x.toBits + 1 by ring] at hw hlo hhi
  obtain ⟨f0, f1, f2, el, b0, b1', b2⟩ := log_val hF hLA x hx (by linarith) (by linarith) lh ll lll hT
  obtain ⟨g0, g1, g2, eg, n0, n1, n2⟩ := neg_triple lh ll lll _ _ f0 f1 f2 el
  have hlx := log_lower (value x.toBits) h1.le
  have hlx2 : Real.log (value x.toBits) < 0 := Real.log_neg (by linarith) (by linarith)
  have hw2 := win_add p0 p1 0.0 (-lh) (-ll) (-lll) _ _ _ _ _ _ hw (by norm_num) (by norm_num)
    (by norm_num) g0 g1 g2 eg (by norm_num) (by rw [n0]; linarith) (by rw [n1]; linarith)
    (by rw [n2]; linarith) (abs_le.mpr ⟨by linarith, by linarith⟩) a1 b1 hS1 h2' l2 hP2 a3 b3 hS3
  rw [rec1 _ (by linarith), show GammaBasic.lgamma (value x.toBits) + Real.log (value x.toBits) +
    -Real.log (value x.toBits) = GammaBasic.lgamma (value x.toBits) by ring] at hw2
  exact win_mono hw2 (by unfold Emid; norm_num) (by norm_num) (by norm_num)

/-! ### The window about 1.5 -/

/-- **The window about 1.5 at a positive argument**: `log Γ x`. -/
theorem w15_pos (hF : FmaSpec.FmaNearest) (hAP : LgammaApprox.AccPolyFact) (x : Float)
    (hx : Finite x.toBits) (h1 : 5 / 4 < value x.toBits) (h2 : value x.toBits < 7 / 4)
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 68 30 (x - 1.5) 0.0 = (p0, p1)) :
    WinSpec (GammaBasic.lgamma (value x.toBits)) Emid (1 / 2 ^ 40) 0 (p0, p1, 0.0) := by
  obtain ⟨df, dv, dD⟩ := win_sub x 1.5 (3 / 2) hx c15.1 c15.2 (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  obtain ⟨hw, -, -⟩ := mid_val hF hAP (x - 1.5) df dD p0 p1 hP
  rw [dv, show 3 / 2 + (value x.toBits - 3 / 2) = value x.toBits by ring] at hw
  exact win_mono hw (by unfold Emid; norm_num) le_rfl le_rfl

set_option maxHeartbeats 2000000 in
/-- **The window about 1.5 at a negative argument**: `log Γ (x + 1) = log Γ x + log x`. -/
theorem w15_neg (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 5 / 4 < value x.toBits) (h2 : value x.toBits < 7 / 4)
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 68 30 (x - 1.5) 0.0 = (p0, p1))
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H x = (lh, ll, lll))
    (a1 b1 : Float) (hS1 : sumDD p1 0.0 ll lll = (a1, b1))
    (h2' l2 : Float) (hP2 : twoSum p0 lh = (h2', l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    WinSpec (GammaBasic.lgamma (value x.toBits + 1)) Emid (1 / 2 ^ 39) (1 / 2 ^ 84)
      (h2', a3, b3) := by
  obtain ⟨df, dv, dD⟩ := win_sub x 1.5 (3 / 2) hx c15.1 c15.2 (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  obtain ⟨hw, hlo, hhi⟩ := mid_val hF hAP (x - 1.5) df dD p0 p1 hP
  rw [dv, show 3 / 2 + (value x.toBits - 3 / 2) = value x.toBits by ring] at hw hlo hhi
  obtain ⟨f0, f1, f2, el, b0, b1', b2⟩ := log_val hF hLA x hx (by linarith) (by linarith) lh ll lll hT
  have hlx := log_upper (value x.toBits) (by linarith)
  have hlx2 : 0 < Real.log (value x.toBits) := Real.log_pos (by linarith)
  have hw2 := win_add p0 p1 0.0 lh ll lll _ _ _ _ _ _ hw (by norm_num) (by norm_num)
    (by norm_num) f0 f1 f2 el (by norm_num) (by linarith) (by linarith) (by linarith)
    (abs_le.mpr ⟨by linarith, by linarith⟩) a1 b1 hS1 h2' l2 hP2 a3 b3 hS3
  rw [← rec1 _ (by linarith)] at hw2
  exact win_mono hw2 (by unfold Emid; norm_num) (by norm_num) (by norm_num)

/-! ### The window about 2.5 -/

set_option maxHeartbeats 2000000 in
/-- **The window about 2.5 at a positive argument**: `log Γ x = log Γ (x - 1) + log (x - 1)`. -/
theorem w25_pos (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 9 / 4 < value x.toBits) (h2 : value x.toBits < 11 / 4)
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 68 30 (x - 2.5) 0.0 = (p0, p1))
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 1.0) = (lh, ll, lll))
    (a1 b1 : Float) (hS1 : sumDD p1 0.0 ll lll = (a1, b1))
    (h2' l2 : Float) (hP2 : twoSum p0 lh = (h2', l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    WinSpec (GammaBasic.lgamma (value x.toBits)) (9 / 2 ^ 61 + 1 / 2 ^ 70 + 1 / 2 ^ 87)
      (1 / 2 ^ 40 + 1 / 2 ^ 45) (1 / 2 ^ 85) (h2', a3, b3) := by
  obtain ⟨df, dv, dD⟩ := win_sub x 2.5 (5 / 2) hx c25.1 c25.2 (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  obtain ⟨hw, hlo, hhi⟩ := mid_val hF hAP (x - 2.5) df dD p0 p1 hP
  rw [dv, show 3 / 2 + (value x.toBits - 5 / 2) = value x.toBits - 1 by ring] at hw hlo hhi
  obtain ⟨yf, yv⟩ := sub_int x 1.0 hx c10.1 1 (by rw [c10.2]; norm_num) le_rfl (by norm_num)
    (by push_cast; linarith) (by linarith)
  push_cast at yv
  obtain ⟨f0, f1, f2, el, b0, b1', b2⟩ := log_val hF hLA (x - 1.0) yf (by rw [yv]; linarith)
    (by rw [yv]; linarith) lh ll lll hT
  rw [yv] at el
  have hlx := log_upper (value x.toBits - 1) (by linarith)
  have hlx2 : 0 < Real.log (value x.toBits - 1) := Real.log_pos (by linarith)
  have hw2 := win_add p0 p1 0.0 lh ll lll _ _ _ _ _ _ hw (by norm_num) (by norm_num)
    (by norm_num) f0 f1 f2 el (by norm_num) (by linarith) (by linarith) (by linarith)
    (abs_le.mpr ⟨by linarith, by linarith⟩) a1 b1 hS1 h2' l2 hP2 a3 b3 hS3
  rw [← rec1 _ (by linarith), sub_add_cancel] at hw2
  exact win_mono hw2 (by norm_num) (by norm_num) (by norm_num)

set_option maxHeartbeats 2000000 in
/-- **The window about 2.5 at a negative argument**: `log Γ (x + 1) = log Γ x + log x`. -/
theorem w25_neg (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 9 / 4 < value x.toBits) (h2 : value x.toBits < 11 / 4)
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 68 30 (x - 2.5) 0.0 = (p0, p1))
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 1.0) = (lh, ll, lll))
    (a1 b1 : Float) (hS1 : sumDD p1 0.0 ll lll = (a1, b1))
    (h2' l2 : Float) (hP2 : twoSum p0 lh = (h2', l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3))
    (mh ml mll : Float) (hM : Lgamma.asLogdAccurate Tgamma.logdTable H x = (mh, ml, mll))
    (a4 b4 : Float) (hS4 : sumDD a3 b3 ml mll = (a4, b4))
    (h5 l5 : Float) (hP5 : twoSum h2' mh = (h5, l5))
    (a6 b6 : Float) (hS6 : sumDD a4 b4 l5 0.0 = (a6, b6)) :
    WinSpec (GammaBasic.lgamma (value x.toBits + 1)) Emid (1 / 2 ^ 39) (1 / 2 ^ 83)
      (h5, a6, b6) := by
  have hw := w25_pos hF hLA hAP x hx h1 h2 p0 p1 hP lh ll lll hT a1 b1 hS1 h2' l2 hP2 a3 b3 hS3
  obtain ⟨f0, f1, f2, el, b0, b1', b2⟩ := log_val hF hLA x hx (by linarith) (by linarith) mh ml mll hM
  have hlx := log_upper (value x.toBits) (by linarith)
  have hlx2 : 0 < Real.log (value x.toBits) := Real.log_pos (by linarith)
  -- `log Γ x` from the window's own bounds
  have hG : |GammaBasic.lgamma (value x.toBits) + Real.log (value x.toBits)| ≤ 7 / 2 := by
    obtain ⟨df, dv, dD⟩ := win_sub x 2.5 (5 / 2) hx c25.1 c25.2 (by norm_num) (by norm_num)
      (by linarith) (by linarith)
    obtain ⟨-, hlo, hhi⟩ := mid_val hF hAP (x - 2.5) df dD p0 p1 hP
    rw [dv, show 3 / 2 + (value x.toBits - 5 / 2) = value x.toBits - 1 by ring] at hlo hhi
    have hr := rec1 (value x.toBits - 1) (by linarith)
    rw [sub_add_cancel] at hr
    have hl1 := log_upper (value x.toBits - 1) (by linarith)
    have hl2 : 0 < Real.log (value x.toBits - 1) := Real.log_pos (by linarith)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hw2 := win_add h2' a3 b3 mh ml mll _ _ _ _ _ _ hw (by norm_num) (by norm_num)
    (by norm_num) f0 f1 f2 el (by norm_num) (by linarith) (by linarith) (by linarith) hG
    a4 b4 hS4 h5 l5 hP5 a6 b6 hS6
  rw [← rec1 _ (by linarith)] at hw2
  exact win_mono hw2 (by unfold Emid; norm_num) (by norm_num) (by norm_num)

/-! ### The window about 3.5 -/

set_option maxHeartbeats 4000000 in
/-- **The window about 3.5 at a positive argument**:
`log Γ x = log Γ (x - 2) + log (x - 1) + log (x - 2)`. -/
theorem w35_pos (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 13 / 4 < value x.toBits) (h2 : value x.toBits < 15 / 4)
    (bh bl bll : Float) (hTb : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 2.0) = (bh, bl, bll))
    (ah al all : Float) (hTa : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 1.0) = (ah, al, all))
    (s1 t1 : Float) (hS1 : sumDD al all bl bll = (s1, t1))
    (s0 u : Float) (hP0 : fastTwoSum ah bh = (s0, u))
    (s1' s2 : Float) (hS2 : sumDD s1 t1 u 0.0 = (s1', s2))
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 68 30 (x - 3.5) 0.0 = (p0, p1))
    (a1 b1 : Float) (hS3 : sumDD p1 0.0 s1' s2 = (a1, b1))
    (h2' l2 : Float) (hP2 : twoSum p0 s0 = (h2', l2))
    (a3 b3 : Float) (hS4 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    WinSpec (GammaBasic.lgamma (value x.toBits)) (9 / 2 ^ 61 + 1 / 2 ^ 70 + 1 / 2 ^ 85)
      (1 / 2 ^ 40 + 1 / 2 ^ 45) (1 / 2 ^ 85) (h2', a3, b3) := by
  obtain ⟨df, dv, dD⟩ := win_sub x 3.5 (7 / 2) hx c35.1 c35.2 (by norm_num) (by norm_num)
    (by linarith) (by linarith)
  obtain ⟨hw, hlo, hhi⟩ := mid_val hF hAP (x - 3.5) df dD p0 p1 hP
  rw [dv, show 3 / 2 + (value x.toBits - 7 / 2) = value x.toBits - 2 by ring] at hw hlo hhi
  obtain ⟨af, av⟩ := sub_int x 1.0 hx c10.1 1 (by rw [c10.2]; norm_num) le_rfl (by norm_num)
    (by push_cast; linarith) (by linarith)
  obtain ⟨bf, bv⟩ := sub_int x 2.0 hx c20.1 2 (by rw [c20.2]; norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by linarith)
  push_cast at av bv
  have hla := log_upper (value x.toBits - 1) (by linarith)
  have hla2 : 0 < Real.log (value x.toBits - 1) := Real.log_pos (by linarith)
  have hlb := log_upper (value x.toBits - 2) (by linarith)
  have hlb2 : 0 < Real.log (value x.toBits - 2) := Real.log_pos (by linarith)
  have hab : Real.log (value x.toBits - 2) + 1 / 2 ^ 40 ≤ Real.log (value x.toBits - 1) := by
    have hq := Real.one_sub_inv_le_log_of_pos
      (show 0 < (value x.toBits - 1) / (value x.toBits - 2) by apply div_pos <;> linarith)
    rw [Real.log_div (by linarith) (by linarith), inv_div] at hq
    have : (value x.toBits - 2) / (value x.toBits - 1) ≤ 13 / 20 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 40 ≤ 7 / 20)]
  obtain ⟨g0, g1, g2, eg, n0, n1, n2⟩ := log_sum hF hLA (x - 1.0) (x - 2.0) af bf
    (by rw [av]; linarith) (by rw [av]; linarith) (by rw [bv]; linarith) (by rw [bv]; linarith)
    (by rw [av, bv]; exact abs_le.mpr ⟨by linarith, by linarith⟩)
    (by rw [av, bv, abs_of_pos hla2, abs_of_pos hlb2]; exact hab)
    bh bl bll hTb ah al all hTa s1 t1 hS1 s0 u hP0 s1' s2 hS2
  rw [av, bv] at eg
  have hw2 := win_add p0 p1 0.0 s0 s1' s2 _ _ _ _ _ _ hw (by norm_num) (by norm_num)
    (by norm_num) g0 g1 g2 eg (by norm_num) n0 n1 n2
    (abs_le.mpr ⟨by linarith, by linarith⟩) a1 b1 hS3 h2' l2 hP2 a3 b3 hS4
  have r1 := rec1 (value x.toBits - 2) (by linarith)
  have r2 := rec1 (value x.toBits - 1) (by linarith)
  rw [show value x.toBits - 2 + 1 = value x.toBits - 1 by ring] at r1
  rw [sub_add_cancel] at r2
  rw [show GammaBasic.lgamma (value x.toBits - 2) + (Real.log (value x.toBits - 1) +
    Real.log (value x.toBits - 2)) = GammaBasic.lgamma (value x.toBits) by linarith] at hw2
  exact win_mono hw2 (by norm_num) (by norm_num) (by norm_num)

set_option maxHeartbeats 4000000 in
/-- **The window about 3.5 at a negative argument**: `log Γ (x + 1) = log Γ x + log x`. -/
theorem w35_neg (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 13 / 4 < value x.toBits) (h2 : value x.toBits < 15 / 4)
    (bh bl bll : Float) (hTb : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 2.0) = (bh, bl, bll))
    (ah al all : Float) (hTa : Lgamma.asLogdAccurate Tgamma.logdTable H (x - 1.0) = (ah, al, all))
    (s1 t1 : Float) (hS1 : sumDD al all bl bll = (s1, t1))
    (s0 u : Float) (hP0 : fastTwoSum ah bh = (s0, u))
    (s1' s2 : Float) (hS2 : sumDD s1 t1 u 0.0 = (s1', s2))
    (p0 p1 : Float) (hP : Lgamma.polyDDDFst Lgamma.accurateTable 68 30 (x - 3.5) 0.0 = (p0, p1))
    (a1 b1 : Float) (hS3 : sumDD p1 0.0 s1' s2 = (a1, b1))
    (h2' l2 : Float) (hP2 : twoSum p0 s0 = (h2', l2))
    (a3 b3 : Float) (hS4 : sumDD a1 b1 l2 0.0 = (a3, b3))
    (mh ml mll : Float) (hM : Lgamma.asLogdAccurate Tgamma.logdTable H x = (mh, ml, mll))
    (a4 b4 : Float) (hS5 : sumDD a3 b3 ml mll = (a4, b4))
    (h5 l5 : Float) (hP5 : twoSum h2' mh = (h5, l5))
    (a6 b6 : Float) (hS6 : sumDD a4 b4 l5 0.0 = (a6, b6)) :
    WinSpec (GammaBasic.lgamma (value x.toBits + 1)) Emid (1 / 2 ^ 39) (1 / 2 ^ 83)
      (h5, a6, b6) := by
  have hw := w35_pos hF hLA hAP x hx h1 h2 bh bl bll hTb ah al all hTa s1 t1 hS1 s0 u hP0 s1' s2
    hS2 p0 p1 hP a1 b1 hS3 h2' l2 hP2 a3 b3 hS4
  obtain ⟨f0, f1, f2, el, b0, b1', b2⟩ := log_val hF hLA x hx (by linarith) (by linarith) mh ml mll hM
  have hlx := log_upper (value x.toBits) (by linarith)
  have hlx2 : 0 < Real.log (value x.toBits) := Real.log_pos (by linarith)
  have hG : |GammaBasic.lgamma (value x.toBits) + Real.log (value x.toBits)| ≤ 7 / 2 := by
    obtain ⟨df, dv, dD⟩ := win_sub x 3.5 (7 / 2) hx c35.1 c35.2 (by norm_num) (by norm_num)
      (by linarith) (by linarith)
    obtain ⟨-, hlo, hhi⟩ := mid_val hF hAP (x - 3.5) df dD p0 p1 hP
    rw [dv, show 3 / 2 + (value x.toBits - 7 / 2) = value x.toBits - 2 by ring] at hlo hhi
    have r1 := rec1 (value x.toBits - 2) (by linarith)
    have r2 := rec1 (value x.toBits - 1) (by linarith)
    rw [show value x.toBits - 2 + 1 = value x.toBits - 1 by ring] at r1
    rw [sub_add_cancel] at r2
    have hla := log_upper (value x.toBits - 1) (by linarith)
    have hla2 : 0 < Real.log (value x.toBits - 1) := Real.log_pos (by linarith)
    have hlb := log_upper (value x.toBits - 2) (by linarith)
    have hlb2 : 0 < Real.log (value x.toBits - 2) := Real.log_pos (by linarith)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hw2 := win_add h2' a3 b3 mh ml mll _ _ _ _ _ _ hw (by norm_num) (by norm_num)
    (by norm_num) f0 f1 f2 el (by norm_num) (by linarith) (by linarith) (by linarith) hG
    a4 b4 hS5 h5 l5 hP5 a6 b6 hS6
  rw [← rec1 _ (by linarith)] at hw2
  exact win_mono hw2 (by unfold Emid; norm_num) (by norm_num) (by norm_num)

#print axioms w05_neg
#print axioms w05_pos
#print axioms w15_pos
#print axioms w15_neg
#print axioms w25_pos
#print axioms w25_neg
#print axioms w35_pos
#print axioms w35_neg

#print axioms mid_val
#print axioms log_val
#print axioms win_add
#print axioms log_sum

end Verified.Examples.LgammaAccWin
