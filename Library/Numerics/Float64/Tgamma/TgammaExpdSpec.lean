import Library.Numerics.Float64.Tgamma.TgammaExpd

/-!
**The specification of `Tgamma.asExpd`** for `1 ≤ x + l ≤ 1000` and `|l| ≤ 2 ^ -40`: the result
`(h, l, E)` satisfies `|(h + l) 2 ^ E - exp (x + l)| ≤ exp (x + l)/2 ^ 59` (`asExpd_spec`).  The proof
combines the reduction of `TgammaExpRed`, the table product (`exp_table`), and the kernel of
`TgammaExpd.exp_poly` with `ExpFact`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaExpdSpec
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaExpr TgammaWords
  TgammaMainRed TgammaFloor TgammaRecip TgammaExpRed TgammaPolyDDD TgammaExpd

set_option exponentiation.threshold 4096

theorem tab_bounds : ∀ i < 32,
    PolyBound.qabs (PolyBound.ratOfWord expdTable[2 * i + 1]!) ≤ 2 ∧
    PolyBound.qabs (PolyBound.ratOfWord expdTable[2 * i]!) ≤ 1 / 2 ^ 53 ∧
    PolyBound.qabs (PolyBound.ratOfWord expdTable[64 + 2 * i + 1]!) ≤ 103 / 100 ∧
    PolyBound.qabs (PolyBound.ratOfWord expdTable[64 + 2 * i]!) ≤ 1 / 2 ^ 53 := by
  decide +kernel

theorem rabs (w : UInt64) (B : ℚ) (h : PolyBound.qabs (PolyBound.ratOfWord w) ≤ B) :
    |(PolyBound.ratOfWord w : ℝ)| ≤ (B : ℝ) := TgammaSmall.abs_rat_le _ _ h

/-- **The table product** `e0 i0 · e1 i1`. -/
theorem exp_table (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (n0 n1 : ℕ) (h0 : n0 < 32) (h1 : n1 < 32) :
    Finite (mulDD (Float.ofBits expdTable[2 * n0 + 1]!) (Float.ofBits expdTable[2 * n0]!)
        (Float.ofBits expdTable[64 + 2 * n1 + 1]!) (Float.ofBits expdTable[64 + 2 * n1]!)).1.toBits ∧
      Finite (mulDD (Float.ofBits expdTable[2 * n0 + 1]!) (Float.ofBits expdTable[2 * n0]!)
        (Float.ofBits expdTable[64 + 2 * n1 + 1]!) (Float.ofBits expdTable[64 + 2 * n1]!)).2.toBits ∧
      |value (mulDD (Float.ofBits expdTable[2 * n0 + 1]!) (Float.ofBits expdTable[2 * n0]!)
          (Float.ofBits expdTable[64 + 2 * n1 + 1]!) (Float.ofBits expdTable[64 + 2 * n1]!)).1.toBits +
        value (mulDD (Float.ofBits expdTable[2 * n0 + 1]!) (Float.ofBits expdTable[2 * n0]!)
          (Float.ofBits expdTable[64 + 2 * n1 + 1]!) (Float.ofBits expdTable[64 + 2 * n1]!)).2.toBits -
        (TgammaApprox.e0 n0 : ℝ) * (TgammaApprox.e1 n1 : ℝ)| ≤ 1 / 2 ^ 100 ∧
      |value (mulDD (Float.ofBits expdTable[2 * n0 + 1]!) (Float.ofBits expdTable[2 * n0]!)
        (Float.ofBits expdTable[64 + 2 * n1 + 1]!) (Float.ofBits expdTable[64 + 2 * n1]!)).2.toBits| ≤
        1 / 2 ^ 49 ∧
      |value (mulDD (Float.ofBits expdTable[2 * n0 + 1]!) (Float.ofBits expdTable[2 * n0]!)
        (Float.ofBits expdTable[64 + 2 * n1 + 1]!) (Float.ofBits expdTable[64 + 2 * n1]!)).1.toBits| ≤
        3 := by
  obtain ⟨b1, b2, -, -⟩ := tab_bounds n0 h0
  obtain ⟨-, -, b3, b4⟩ := tab_bounds n1 h1
  have v1 := wv (2 * n0 + 1) (by omega)
  have v2 := wv (2 * n0) (by omega)
  have v3 := wv (64 + 2 * n1 + 1) (by omega)
  have v4 := wv (64 + 2 * n1) (by omega)
  have a1 : |value (Float.ofBits expdTable[2 * n0 + 1]!).toBits| ≤ 2 := by
    rw [v1]; have := rabs _ _ b1; push_cast at this; exact this
  have a2 : |value (Float.ofBits expdTable[2 * n0]!).toBits| ≤ 1 / 2 ^ 53 := by
    rw [v2]; have := rabs _ _ b2; push_cast at this; exact this
  have a3 : |value (Float.ofBits expdTable[64 + 2 * n1 + 1]!).toBits| ≤ 103 / 100 := by
    rw [v3]; have := rabs _ _ b3; push_cast at this; exact this
  have a4 : |value (Float.ofBits expdTable[64 + 2 * n1]!).toBits| ≤ 1 / 2 ^ 53 := by
    rw [v4]; have := rabs _ _ b4; push_cast at this; exact this
  obtain ⟨h1f, h2f, he, hlow, hhigh⟩ := mulDD_spec hF _ _ _ _ (wf _ (by omega)) (wf _ (by omega))
    (wf _ (by omega)) (wf _ (by omega)) (103 / 100 * 2) (103 / 100 * (1 / 2 ^ 53))
    (1 / 2 ^ 53 * 2) (1 / 2 ^ 53 * (1 / 2 ^ 53))
    (mul_le_mul a3 a1 (abs_nonneg _) (by norm_num)) (mul_le_mul a3 a2 (abs_nonneg _) (by norm_num))
    (mul_le_mul a4 a1 (abs_nonneg _) (by norm_num)) (mul_le_mul a4 a2 (abs_nonneg _) (by norm_num))
    (by norm_num) (by norm_num)
  have htarget : (value (Float.ofBits expdTable[2 * n0 + 1]!).toBits +
      value (Float.ofBits expdTable[2 * n0]!).toBits) *
      (value (Float.ofBits expdTable[64 + 2 * n1 + 1]!).toBits +
      value (Float.ofBits expdTable[64 + 2 * n1]!).toBits) =
      (TgammaApprox.e0 n0 : ℝ) * (TgammaApprox.e1 n1 : ℝ) := by
    rw [v1, v2, v3, v4, TgammaApprox.e0, TgammaApprox.e1, show 65 + 2 * n1 = 64 + 2 * n1 + 1 by omega]
    simp only [TgammaApprox.q]
    push_cast
    ring
  rw [htarget] at he
  refine ⟨h1f, h2f, he.trans (by norm_num), hlow.trans (by norm_num), hhigh.trans (by norm_num)⟩

/-- The real-number part of `asExpd_spec`. -/
theorem exp_assemble (hE : TgammaApprox.ExpFact) (Y p X q1 c r V : ℝ) (K E n0 n1 : ℕ)
    (hY1 : 1 ≤ Y) (hY2 : Y ≤ 1000)
    (hp : |p - Y * TgammaApprox.invLn2| ≤ 1 / 2 ^ 54)
    (hX : |X - (p - K)| ≤ 1 / 2 ^ 53) (hq1 : |q1| ≤ 61 / 100) (hXq : |X - q1| ≤ 1 / 2 ^ 52)
    (hc : |c - (1 + q1 * TgammaApprox.expPoly q1)| ≤ 1 / 2 ^ 61)
    (hr : |r - (TgammaApprox.e0 n0 : ℝ) * (TgammaApprox.e1 n1 : ℝ)| ≤ 1 / 2 ^ 100)
    (hV : |V - r * c| ≤ 1 / 2 ^ 96)
    (hK : K = 1024 * E + 32 * n0 + n1) (hn0 : n0 < 32) (hn1 : n1 < 32) :
    |V * 2 ^ E - Real.exp Y| ≤ Real.exp Y / 2 ^ 59 ∧ 99 / 100 ≤ V ∧ V ≤ 212 / 100 := by
  obtain ⟨hinv, he0, he1, hpoly⟩ := hE
  have hl2lo := Real.log_two_gt_d9
  have hl2hi := Real.log_two_lt_d9
  set L := Real.log 2 with hL
  have hL0 : 0 < L := by linarith
  -- the reduced argument `D`
  set Ts := Y * (1024 / L) with hTs
  have hTsY : |Y * TgammaApprox.invLn2 - Ts| ≤ 1000 / 2 ^ 80 := by
    rw [hTs, ← mul_sub, abs_mul, abs_of_pos (by linarith)]
    calc Y * |(TgammaApprox.invLn2 : ℝ) - 1024 / L| ≤ 1000 * (1 / 2 ^ 80) :=
          mul_le_mul hY2 hinv (abs_nonneg _) (by norm_num)
      _ = 1000 / 2 ^ 80 := by ring
  set D := Ts - K with hD
  have hqD : |q1 - D| ≤ 1 / 2 ^ 51 := by
    have h1 := abs_sub_abs_le_abs_sub (q1 - D) 0
    have : q1 - D = -(X - q1) + (X - (p - K)) + (p - Y * TgammaApprox.invLn2) +
        (Y * TgammaApprox.invLn2 - Ts) := by rw [hD]; ring
    rw [this]
    have e1 := abs_add_le (-(X - q1) + (X - (p - K)) + (p - Y * TgammaApprox.invLn2))
      (Y * TgammaApprox.invLn2 - Ts)
    have e2 := abs_add_le (-(X - q1) + (X - (p - K))) (p - Y * TgammaApprox.invLn2)
    have e3 := abs_add_le (-(X - q1)) (X - (p - K))
    rw [abs_neg] at e3
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 + 1 / 2 ^ 53 + 1 / 2 ^ 54 + 1000 / 2 ^ 80 ≤
      1 / 2 ^ 51)]
  have hDb : |D| ≤ 62 / 100 := by
    have h1 := abs_sub_abs_le_abs_sub D q1
    have h2 : |D - q1| = |q1 - D| := abs_sub_comm _ _
    linarith [(by norm_num : (61 : ℝ) / 100 + 1 / 2 ^ 51 ≤ 62 / 100)]
  -- `Z = exp (D ln 2/1024)`
  set Z := Real.exp (D * L / 1024) with hZ
  have hZ1 : |Z - 1| ≤ 1 / 1000 := by
    have harg : |D * L / 1024| ≤ 1 / 2000 := by
      rw [abs_div, abs_mul, abs_of_pos hL0, abs_of_pos (by norm_num : (0 : ℝ) < 1024),
        div_le_iff₀ (by norm_num)]
      calc |D| * L ≤ 62 / 100 * 0.6931471808 := mul_le_mul hDb hl2hi.le hL0.le (by norm_num)
        _ ≤ 1 / 2000 * 1024 := by norm_num
    have := Real.abs_exp_sub_one_le (le_trans harg (by norm_num))
    linarith
  have hZlo : 999 / 1000 ≤ Z := by linarith [(abs_le.mp hZ1).1]
  have hZhi : Z ≤ 1001 / 1000 := by linarith [(abs_le.mp hZ1).2]
  -- the kernel at `q1`
  have hk := hpoly q1 (by linarith [(by norm_num : (61 : ℝ) / 100 ≤ 5 / 8)])
  have hsplit : Real.exp (q1 * L / 1024) = Z * Real.exp ((q1 - D) * L / 1024) := by
    rw [hZ, ← Real.exp_add]
    congr 1
    ring
  have hq1Z : |Real.exp (q1 * L / 1024) - Z| ≤ 7 / 10 * Z / 2 ^ 60 := by
    have harg : |(q1 - D) * L / 1024| ≤ 1 / 2 ^ 51 * L / 1024 := by
      rw [abs_div, abs_mul, abs_of_pos hL0, abs_of_pos (by norm_num : (0 : ℝ) < 1024)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hqD hL0.le) (by norm_num)
    have h1 := Real.abs_exp_sub_one_le (le_trans harg (by
      rw [div_le_one (by norm_num)]; linarith))
    rw [hsplit, show Z * Real.exp ((q1 - D) * L / 1024) - Z =
      Z * (Real.exp ((q1 - D) * L / 1024) - 1) by ring, abs_mul, abs_of_pos (by linarith)]
    have h2 : 2 * |(q1 - D) * L / 1024| ≤ 7 / 10 / 2 ^ 60 := by
      have : 2 * (1 / 2 ^ 51 * L / 1024) ≤ 7 / 10 / 2 ^ 60 := by
        rw [show 2 * (1 / 2 ^ 51 * L / 1024) = L / 2 ^ 60 by ring]
        exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
      linarith
    have := mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith : (0 : ℝ) ≤ Z)
    linarith
  have hcZ : |c - Z| ≤ 1 / 2 ^ 61 + 1 / 2 ^ 74 + 7 / 10 * Z / 2 ^ 60 := by
    have : c - Z = (c - (1 + q1 * TgammaApprox.expPoly q1)) +
        ((1 + q1 * TgammaApprox.expPoly q1) - Real.exp (q1 * L / 1024)) +
        (Real.exp (q1 * L / 1024) - Z) := by ring
    rw [this]
    have e1 := abs_add_le ((c - (1 + q1 * TgammaApprox.expPoly q1)) +
        ((1 + q1 * TgammaApprox.expPoly q1) - Real.exp (q1 * L / 1024))) (Real.exp (q1 * L / 1024) - Z)
    have e2 := abs_add_le (c - (1 + q1 * TgammaApprox.expPoly q1))
        ((1 + q1 * TgammaApprox.expPoly q1) - Real.exp (q1 * L / 1024))
    rw [abs_sub_comm (1 + q1 * TgammaApprox.expPoly q1)] at e2
    have hk' : |Real.exp (q1 * L / 1024) - (1 + q1 * TgammaApprox.expPoly q1)| ≤
      1 / 2 ^ 74 := hk
    linarith
  -- the tables
  set A0 := Real.exp (n0 * L / 32) with hA0
  set A1 := Real.exp (n1 * L / 1024) with hA1
  have hn0R : (n0 : ℝ) ≤ 31 := by exact_mod_cast (show n0 ≤ 31 by omega)
  have hn1R : (n1 : ℝ) ≤ 31 := by exact_mod_cast (show n1 ≤ 31 by omega)
  have hn00 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
  have hn10 : (0 : ℝ) ≤ n1 := Nat.cast_nonneg _
  have hA0lo : 1 ≤ A0 := Real.one_le_exp (by positivity)
  have hA0hi : A0 ≤ 2 := by
    rw [hA0, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← hL]
    have := mul_le_mul_of_nonneg_right hn0R hL0.le
    exact Real.exp_le_exp.mpr (by linarith)
  have hA1lo : 1 ≤ A1 := Real.one_le_exp (by positivity)
  have hA1hi : A1 ≤ 105 / 100 := by
    have harg : |(n1 : ℝ) * L / 1024| ≤ 1 / 40 := by
      rw [abs_of_nonneg (by positivity), div_le_iff₀ (by norm_num)]
      have := mul_le_mul_of_nonneg_right hn1R hL0.le
      linarith
    have := Real.abs_exp_sub_one_le (le_trans harg (by norm_num))
    linarith [(abs_le.mp this).2]
  have he0' : |(TgammaApprox.e0 n0 : ℝ) - A0| ≤ 1 / 2 ^ 80 := he0 n0 hn0
  have he1' : |(TgammaApprox.e1 n1 : ℝ) - A1| ≤ 1 / 2 ^ 80 := he1 n1 hn1
  have hW : |(TgammaApprox.e0 n0 : ℝ) * (TgammaApprox.e1 n1 : ℝ) - A0 * A1| ≤ 1 / 2 ^ 78 := by
    have : (TgammaApprox.e0 n0 : ℝ) * (TgammaApprox.e1 n1 : ℝ) - A0 * A1 =
        ((TgammaApprox.e0 n0 : ℝ) - A0) * (TgammaApprox.e1 n1 : ℝ) +
          A0 * ((TgammaApprox.e1 n1 : ℝ) - A1) := by ring
    rw [this]
    have e1 := abs_add_le (((TgammaApprox.e0 n0 : ℝ) - A0) * (TgammaApprox.e1 n1 : ℝ))
      (A0 * ((TgammaApprox.e1 n1 : ℝ) - A1))
    have he1b : |(TgammaApprox.e1 n1 : ℝ)| ≤ 106 / 100 := by
      have := abs_sub_abs_le_abs_sub (TgammaApprox.e1 n1 : ℝ) A1
      rw [abs_of_pos (by linarith : (0 : ℝ) < A1)] at this
      linarith [(by norm_num : (105 : ℝ) / 100 + 1 / 2 ^ 80 ≤ 106 / 100)]
    have e2 : |((TgammaApprox.e0 n0 : ℝ) - A0) * (TgammaApprox.e1 n1 : ℝ)| ≤
        1 / 2 ^ 80 * (106 / 100) := by
      rw [abs_mul]; exact mul_le_mul he0' he1b (abs_nonneg _) (by norm_num)
    have e3 : |A0 * ((TgammaApprox.e1 n1 : ℝ) - A1)| ≤ 2 * (1 / 2 ^ 80) := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < A0)]
      exact mul_le_mul hA0hi he1' (abs_nonneg _) (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 80 * (106 / 100) + 2 * (1 / 2 ^ 80) ≤ 1 / 2 ^ 78)]
  have hrW : |r - A0 * A1| ≤ 1 / 2 ^ 77 := by
    have := abs_add_le (r - (TgammaApprox.e0 n0 : ℝ) * (TgammaApprox.e1 n1 : ℝ))
      ((TgammaApprox.e0 n0 : ℝ) * (TgammaApprox.e1 n1 : ℝ) - A0 * A1)
    rw [show r - (TgammaApprox.e0 n0 : ℝ) * (TgammaApprox.e1 n1 : ℝ) +
      ((TgammaApprox.e0 n0 : ℝ) * (TgammaApprox.e1 n1 : ℝ) - A0 * A1) = r - A0 * A1 by ring] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 100 + 1 / 2 ^ 78 ≤ 1 / 2 ^ 77)]
  -- the product
  set W := A0 * A1 with hWdef
  have hW1 : 1 ≤ W := one_le_mul_of_one_le_of_one_le hA0lo hA1lo
  have hW2 : W ≤ 21 / 10 := by
    have := mul_le_mul hA0hi hA1hi (by linarith) (by norm_num)
    linarith
  have hWZ : 999 / 1000 * W ≤ W * Z := by
    have := mul_le_mul_of_nonneg_left hZlo (by linarith : (0 : ℝ) ≤ W)
    linarith
  have hWZ2 : W * Z ≤ 1001 / 1000 * W := by
    have := mul_le_mul_of_nonneg_left hZhi (by linarith : (0 : ℝ) ≤ W)
    linarith
  have hcb : |c| ≤ 1002 / 1000 := by
    have := abs_sub_abs_le_abs_sub c Z
    rw [abs_of_pos (by linarith : (0 : ℝ) < Z)] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 61 + 1 / 2 ^ 74 + 7 / 10 * (1001 / 1000) / 2 ^ 60 ≤ 1 / 1000)]
  have hmain : |V - W * Z| ≤ W * Z / 2 ^ 59 := by
    have hs : V - W * Z = (V - r * c) + (r - W) * c + W * (c - Z) := by ring
    rw [hs]
    have e1 := abs_add_le ((V - r * c) + (r - W) * c) (W * (c - Z))
    have e2 := abs_add_le (V - r * c) ((r - W) * c)
    have f1 : |(r - W) * c| ≤ 1 / 2 ^ 77 * (1002 / 1000) := by
      rw [abs_mul]; exact mul_le_mul hrW hcb (abs_nonneg _) (by norm_num)
    have f2 : |W * (c - Z)| ≤ W * (1 / 2 ^ 61 + 1 / 2 ^ 74) + 7 / 10 * (W * Z) / 2 ^ 60 := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < W)]
      have := mul_le_mul_of_nonneg_left hcZ (by linarith : (0 : ℝ) ≤ W)
      linarith
    linarith
  -- the identity `exp Y = 2 ^ E A0 A1 Z`
  have hYid : Y = E * L + n0 * L / 32 + n1 * L / 1024 + D * L / 1024 := by
    have hKR : (K : ℝ) = 1024 * E + 32 * n0 + n1 := by rw [hK]; push_cast; ring
    have : D = Y * (1024 / L) - K := by rw [hD, hTs]
    rw [this, hKR]
    field_simp
    ring
  have hexp : Real.exp Y = 2 ^ E * (W * Z) := by
    rw [hYid, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [hWdef]
    ring
  rw [hexp]
  have h2E : (0 : ℝ) < 2 ^ E := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [show V * 2 ^ E - 2 ^ E * (W * Z) = 2 ^ E * (V - W * Z) by ring, abs_mul,
      abs_of_pos h2E, show 2 ^ E * (W * Z) / 2 ^ 59 = 2 ^ E * (W * Z / 2 ^ 59) by ring]
    exact mul_le_mul_of_nonneg_left hmain h2E.le
  · have := (abs_le.mp hmain).1
    linarith
  · have := (abs_le.mp hmain).2
    linarith

theorem idx_all : ∀ n < 32, (2 * UInt64.ofNat n + 1).toNat = 2 * n + 1 ∧
    (2 * UInt64.ofNat n).toNat = 2 * n ∧ (64 + 2 * UInt64.ofNat n + 1).toNat = 64 + 2 * n + 1 ∧
    (64 + 2 * UInt64.ofNat n).toNat = 64 + 2 * n := by decide

theorem invLn2_bounds : (1477 : ℚ) ≤ TgammaApprox.invLn2 ∧ TgammaApprox.invLn2 ≤ 1478 := by
  decide +kernel

/-- **`Tgamma.asExpd`** for `1 ≤ x + l ≤ 1000` and `|l| ≤ 2 ^ -14`. -/
theorem asExpd_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hE : TgammaApprox.ExpFact) (x l : Float)
    (hx : Finite x.toBits) (hl : Finite l.toBits) (h1 : 1 ≤ value x.toBits + value l.toBits)
    (h2 : value x.toBits + value l.toBits ≤ 1000) (hlb : |value l.toBits| ≤ 1 / 2 ^ 14) :
    ∃ E : ℕ, E ≤ 1500 ∧ (asExpd expdTable x l).2.2 = UInt64.ofNat E ∧
      Finite (asExpd expdTable x l).1.toBits ∧ Finite (asExpd expdTable x l).2.1.toBits ∧
      |(value (asExpd expdTable x l).1.toBits + value (asExpd expdTable x l).2.1.toBits) * 2 ^ E -
          Real.exp (value x.toBits + value l.toBits)| ≤
        Real.exp (value x.toBits + value l.toBits) / 2 ^ 59 ∧
      |value (asExpd expdTable x l).2.1.toBits| ≤ 1 / 2 ^ 45 ∧
      1 / 2 ≤ value (asExpd expdTable x l).1.toBits ∧ value (asExpd expdTable x l).1.toBits ≤ 5 / 2 := by
  obtain ⟨hp1f, hp2f, hpe, hp2b, hp1b⟩ := exp_mulc hF x l hx hl
    (by rw [abs_le]; constructor <;> linarith) hlb
  have hinv1 : (1477 : ℝ) ≤ TgammaApprox.invLn2 := by exact_mod_cast invLn2_bounds.1
  have hinv2 : (TgammaApprox.invLn2 : ℝ) ≤ 1478 := by exact_mod_cast invLn2_bounds.2
  unfold asExpd
  dsimp only
  generalize mulDD x l (Float.ofBits 0x40971547652B82FE) (Float.ofBits 0x3D1777D0FFDA0D24) = p
    at hp1f hp2f hpe hp2b hp1b ⊢
  obtain ⟨p1, p2⟩ := p
  dsimp only at hp1f hp2f hpe hp2b hp1b ⊢
  set Y := value x.toBits + value l.toBits with hY
  have hYi : 1477 ≤ Y * TgammaApprox.invLn2 := by nlinarith
  have hYi2 : Y * TgammaApprox.invLn2 ≤ 1478000 := by nlinarith
  obtain ⟨hpe1, hpe2⟩ := abs_le.mp hpe
  obtain ⟨hp2b1, hp2b2⟩ := abs_le.mp hp2b
  have hp1lo : 1000 ≤ value p1.toBits := by linarith
  obtain ⟨K, hKv, hK22, hixf, hq1f, hq2f, hqe, hq1b, hq2b⟩ :=
    exp_red p1 p2 hp1f hp2f hp2b hp1lo (by linarith [(abs_le.mp hp1b).2])
  rw [toWord_nat (roundEven p1) K hixf hKv.symm (by omega)]
  generalize fastTwoSum (p1 - roundEven p1) p2 = q at hq1f hq2f hqe hq1b hq2b ⊢
  obtain ⟨q1, q2⟩ := q
  dsimp only at hq1f hq2f hqe hq1b hq2b ⊢
  obtain ⟨hi0, hi1, hsar⟩ := exp_index K (by omega)
  rw [hsar]
  have hs : UInt64.size = 2 ^ 64 := rfl
  have hn0 : K / 32 % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have hn1 : K % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have hi0' : (UInt64.ofNat K >>> 5 &&& 31) = UInt64.ofNat (K / 32 % 32) :=
    UInt64.toNat_inj.mp (by rw [hi0, UInt64.toNat_ofNat_of_lt' (by omega)])
  have hi1' : (UInt64.ofNat K &&& 31) = UInt64.ofNat (K % 32) :=
    UInt64.toNat_inj.mp (by rw [hi1, UInt64.toNat_ofNat_of_lt' (by omega)])
  rw [hi0', hi1']
  obtain ⟨ix1, ix2, -, -⟩ := idx_all _ hn0
  obtain ⟨-, -, ix3, ix4⟩ := idx_all _ hn1
  rw [entry_eq _ _ _ ix1, entry_eq _ _ _ ix2, entry_eq _ _ _ ix3, entry_eq _ _ _ ix4, ← pfl_eq q1]
  -- the table product
  obtain ⟨hr1f, hr2f, hre, hr2b, hr1b⟩ := exp_table hF _ _ hn0 hn1
  generalize mulDD (Float.ofBits expdTable[2 * (K / 32 % 32) + 1]!)
    (Float.ofBits expdTable[2 * (K / 32 % 32)]!) (Float.ofBits expdTable[64 + 2 * (K % 32) + 1]!)
    (Float.ofBits expdTable[64 + 2 * (K % 32)]!) = r at hr1f hr2f hre hr2b hr1b ⊢
  obtain ⟨r1, r2⟩ := r
  dsimp only at hr1f hr2f hre hr2b hr1b ⊢
  -- the kernel
  obtain ⟨hc1f, hef, hce, hc1b, heb⟩ := exp_poly hF q1 q2 hq1f hq2f
    (by linarith [(by norm_num : (61 : ℝ) / 100 ≤ 5 / 8)]) hq2b
  generalize fastTwoSum (entry expdTable 128) (evalF pE q1) = a at hc1f hef hce hc1b heb ⊢
  obtain ⟨a1, a2⟩ := a
  dsimp only at hc1f hef hce hc1b heb ⊢
  generalize mulDD q1 q2 a1 (a2 + entry expdTable 129) = b at hc1f hef hce hc1b heb ⊢
  obtain ⟨b1, b2⟩ := b
  dsimp only at hc1f hef hce hc1b heb ⊢
  generalize fastTwoSum 1.0 b1 = c at hc1f hef hce hc1b heb ⊢
  obtain ⟨c1, c2⟩ := c
  dsimp only at hc1f hef hce hc1b heb ⊢
  -- the final product
  have hr10 := abs_nonneg (value r1.toBits)
  have hr20 := abs_nonneg (value r2.toBits)
  obtain ⟨hf1f, hf2f, hfe, hflow, -⟩ := mulDD_spec hF r1 r2 c1 (b2 + c2) hr1f hr2f hc1f hef
    (2 * 3) (2 * (1 / 2 ^ 49)) (1 / 2 ^ 49 * 3) (1 / 2 ^ 49 * (1 / 2 ^ 49))
    (mul_le_mul hc1b hr1b hr10 (by norm_num)) (mul_le_mul hc1b hr2b hr20 (by norm_num))
    (mul_le_mul heb hr1b hr10 (by norm_num)) (mul_le_mul heb hr2b hr20 (by norm_num))
    (by norm_num) (by norm_num)
  generalize mulDD r1 r2 c1 (b2 + c2) = f at hf1f hf2f hfe hflow ⊢
  obtain ⟨f1, f2⟩ := f
  dsimp only at hf1f hf2f hfe hflow ⊢
  have hf2 : |value f2.toBits| ≤ 1 / 2 ^ 45 := hflow.trans (by norm_num)
  obtain ⟨hA, hV1, hV2⟩ := exp_assemble hE Y (value p1.toBits + value p2.toBits)
    (value q1.toBits + value q2.toBits) (value q1.toBits)
    (value c1.toBits + value (b2 + c2).toBits) (value r1.toBits + value r2.toBits)
    (value f1.toBits + value f2.toBits) K (K / 1024) (K / 32 % 32) (K % 32) h1 h2 hpe hqe hq1b
    (by rw [add_sub_cancel_left]; exact hq2b) hce hre (hfe.trans (by norm_num)) (by omega) hn0 hn1
  refine ⟨K / 1024, ?_, rfl, hf1f, hf2f, hA, hf2, ?_, ?_⟩
  · have : (K : ℝ) ≤ 1478002 := by
      have := abs_le.mp hqe
      linarith [(abs_le.mp hq1b).1, (abs_le.mp hq2b).1]
    have : K ≤ 1478002 := by exact_mod_cast this
    omega
  · linarith [(abs_le.mp hf2).2]
  · linarith [(abs_le.mp hf2).1]

#print axioms exp_table
#print axioms exp_assemble
#print axioms asExpd_spec

end Library.Numerics.Float64.Tgamma.TgammaExpdSpec
