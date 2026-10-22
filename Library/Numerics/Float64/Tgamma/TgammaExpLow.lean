import Library.Numerics.Float64.Tgamma.TgammaExpdSpec

/-!
The low part of `Tgamma.asExpd` below `2 ^ -50` of its high part (`asExpd_low`), which the path of
`tgammaWith` below `-170` needs to place `π/(sin (π d) Γ (1 - x))` against the boundary
`2 ^ -1022`.  The result is `mulDD r1 r2 c1 e` with the table product `r1 + r2` and the kernel
`c1 + e`.  The low parts of the tables lie below `2 ^ -53` of their high parts, so `|r2|` stays below
`4.01 · 2 ^ -53 |r1|` (`table_low`).  The kernel's low part `e` is the rounded sum of the low part
of `mulDD`, below `2 ^ -59`, and the error of `fastTwoSum 1 b1`, which is the rounding error of
`1 + b1` and stays below `|1 + b1|/2 ^ 53` (`kernel_low`).  The final product then has a low part
below `7.1 · 2 ^ -53` of its high part.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaExpLow
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaExpr TgammaWords
  TgammaMainRed TgammaFloor TgammaRecip TgammaExpRed TgammaPolyDDD TgammaExpd TgammaExpdSpec

set_option exponentiation.threshold 4096

theorem tab_ratio : ∀ i < 32,
    PolyBound.qabs (PolyBound.ratOfWord expdTable[2 * i]!) ≤
      PolyBound.qabs (PolyBound.ratOfWord expdTable[2 * i + 1]!) / 2 ^ 53 ∧
    PolyBound.qabs (PolyBound.ratOfWord expdTable[64 + 2 * i]!) ≤
      PolyBound.qabs (PolyBound.ratOfWord expdTable[64 + 2 * i + 1]!) / 2 ^ 53 ∧
    1 ≤ PolyBound.qabs (PolyBound.ratOfWord expdTable[2 * i + 1]!) ∧
    1 ≤ PolyBound.qabs (PolyBound.ratOfWord expdTable[64 + 2 * i + 1]!) := by
  decide +kernel

theorem qabs_real (w : UInt64) : ((PolyBound.qabs (PolyBound.ratOfWord w) : ℚ) : ℝ) =
    |(PolyBound.ratOfWord w : ℝ)| := TgammaExpr.qabs_cast _

/-- A rounded product is at least `|a b| (1 - 2 ^ -53) - 2 ^ -1075` in magnitude. -/
theorem mul_lower (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hm : |value a.toBits| * |value b.toBits| ≤ 2 ^ 1000) :
    |value a.toBits| * |value b.toBits| * (1 - 1 / 2 ^ 53) - 1 / 2 ^ 1075 ≤
      |value (a * b).toBits| := by
  have h := fapprox_mul (fapprox_self a ha) (fapprox_self b hb) |value a.toBits| |value b.toBits|
    le_rfl le_rfl (|value a.toBits| * |value b.toBits|) (by simp)
    (by linarith [(by norm_num : (2 : ℝ) ^ 1000 < 2 ^ 1022)])
  have h2 := h.2
  simp only [zero_mul, mul_zero, add_zero, zero_add] at h2
  have h3 := abs_sub_abs_le_abs_sub (value a.toBits * value b.toBits) (value (a * b).toBits)
  rw [abs_sub_comm (value a.toBits * value b.toBits), abs_mul] at h3
  linarith

/-- **The table product** has a low part below `4.01 · 2 ^ -53` of its high part. -/
theorem table_low (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (n0 n1 : ℕ) (h0 : n0 < 32) (h1 : n1 < 32) :
    1 / 2 ≤ |value (mulDD (Float.ofBits expdTable[2 * n0 + 1]!) (Float.ofBits expdTable[2 * n0]!)
        (Float.ofBits expdTable[64 + 2 * n1 + 1]!) (Float.ofBits expdTable[64 + 2 * n1]!)).1.toBits| ∧
    |value (mulDD (Float.ofBits expdTable[2 * n0 + 1]!) (Float.ofBits expdTable[2 * n0]!)
        (Float.ofBits expdTable[64 + 2 * n1 + 1]!) (Float.ofBits expdTable[64 + 2 * n1]!)).2.toBits| ≤
      |value (mulDD (Float.ofBits expdTable[2 * n0 + 1]!) (Float.ofBits expdTable[2 * n0]!)
        (Float.ofBits expdTable[64 + 2 * n1 + 1]!) (Float.ofBits expdTable[64 + 2 * n1]!)).1.toBits| *
        (401 / 100 / 2 ^ 53) := by
  obtain ⟨r1, r2, r3, -⟩ := tab_ratio n0 h0
  obtain ⟨-, s2, -, s4⟩ := tab_ratio n1 h1
  have cast_le : ∀ a b : ℚ, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun a b h => by exact_mod_cast h
  have v1 := wv (2 * n0 + 1) (by omega)
  have v2 := wv (2 * n0) (by omega)
  have v3 := wv (64 + 2 * n1 + 1) (by omega)
  have v4 := wv (64 + 2 * n1) (by omega)
  have hA1 : 1 ≤ |value (Float.ofBits expdTable[2 * n0 + 1]!).toBits| := by
    have := cast_le _ _ r3; push_cast at this; rw [qabs_real] at this; rw [v1]; exact this
  have hB1 : 1 ≤ |value (Float.ofBits expdTable[64 + 2 * n1 + 1]!).toBits| := by
    have := cast_le _ _ s4; push_cast at this; rw [qabs_real] at this; rw [v3]; exact this
  have ha2 : |value (Float.ofBits expdTable[2 * n0]!).toBits| ≤
      |value (Float.ofBits expdTable[2 * n0 + 1]!).toBits| / 2 ^ 53 := by
    have := cast_le _ _ r1; push_cast at this; rw [qabs_real, qabs_real] at this
    rw [v1, v2]; exact this
  have hb2 : |value (Float.ofBits expdTable[64 + 2 * n1]!).toBits| ≤
      |value (Float.ofBits expdTable[64 + 2 * n1 + 1]!).toBits| / 2 ^ 53 := by
    have := cast_le _ _ s2; push_cast at this; rw [qabs_real, qabs_real] at this
    rw [v3, v4]; exact this
  have hA2 : |value (Float.ofBits expdTable[2 * n0 + 1]!).toBits| ≤ 2 := by
    obtain ⟨b1, -, -, -⟩ := tab_bounds n0 h0
    have := rabs _ _ b1; push_cast at this; rw [v1]; exact this
  have hB2 : |value (Float.ofBits expdTable[64 + 2 * n1 + 1]!).toBits| ≤ 2 := by
    obtain ⟨-, -, b3, -⟩ := tab_bounds n1 h1
    have := rabs _ _ b3; push_cast at this; rw [v3]; linarith
  obtain ⟨H, hH⟩ : ∃ H, H = |value (Float.ofBits expdTable[64 + 2 * n1 + 1]!).toBits| *
      |value (Float.ofBits expdTable[2 * n0 + 1]!).toBits| := ⟨_, rfl⟩
  have hH1 : 1 ≤ H := by rw [hH]; exact one_le_mul_of_one_le_of_one_le hB1 hA1
  have hH4 : H ≤ 4 := by
    rw [hH]; nlinarith [abs_nonneg (value (Float.ofBits expdTable[2 * n0 + 1]!).toBits)]
  obtain ⟨-, -, -, hlow, -⟩ := mulDD_spec hF _ _ _ _ (wf _ (by omega)) (wf _ (by omega))
    (wf _ (by omega)) (wf _ (by omega)) H (H / 2 ^ 53) (H / 2 ^ 53) (H / 2 ^ 106)
    (le_of_eq hH.symm)
    (le_trans (mul_le_mul_of_nonneg_left ha2 (abs_nonneg _)) (le_of_eq (by rw [hH]; ring)))
    (le_trans (mul_le_mul_of_nonneg_right hb2 (abs_nonneg _)) (le_of_eq (by rw [hH]; ring)))
    (le_trans (mul_le_mul hb2 ha2 (abs_nonneg _) (div_nonneg (abs_nonneg _) (by norm_num))) (le_of_eq (by rw [hH]; ring)))
    (by linarith) (by linarith)
  have hlo := mul_lower _ _ (wf (64 + 2 * n1 + 1) (by omega)) (wf (2 * n0 + 1) (by omega))
    (by rw [← hH]; linarith)
  rw [← hH] at hlo
  have hhi : (mulDD (Float.ofBits expdTable[2 * n0 + 1]!) (Float.ofBits expdTable[2 * n0]!)
      (Float.ofBits expdTable[64 + 2 * n1 + 1]!) (Float.ofBits expdTable[64 + 2 * n1]!)).1 =
      Float.ofBits expdTable[64 + 2 * n1 + 1]! * Float.ofBits expdTable[2 * n0 + 1]! := rfl
  rw [hhi]
  exact ⟨by linarith, by linarith⟩

/-- **The kernel's low part** `b2 + c2` below `1.05 · 2 ^ -53` of its high part `c1`. -/
theorem kernel_low (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (q1 q2 : Float) (hq1f : Finite q1.toBits)
    (hq2f : Finite q2.toBits) (hq1 : |value q1.toBits| ≤ 5 / 8)
    (hq2 : |value q2.toBits| ≤ 1 / 2 ^ 52) :
    99 / 100 ≤ |value (fastTwoSum 1.0 (mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
        ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).1).1.toBits| ∧
      |value ((mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
        ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).2 +
        (fastTwoSum 1.0 (mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
        ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).1).2).toBits| ≤
      |value (fastTwoSum 1.0 (mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
        ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).1).1.toBits| *
        (21 / 20 / 2 ^ 53) := by
  -- the tail in double arithmetic
  have hq1' : |value q1.toBits| ≤ (Xq : ℝ) := by rw [Xq]; push_cast; exact hq1
  obtain ⟨hfl, hflm⟩ := evalF_approx pE Xq q1 hq1f hq1' pE_ok
  have hfle : |value (evalF pE q1).toBits - evalR pE (value q1.toBits)| ≤ 1 / 2 ^ 74 := by
    have h := hfl.2
    have : ((bnd pE Xq).2 : ℝ) ≤ ((1 / 2 ^ 74 : ℚ) : ℝ) := by exact_mod_cast pE_err
    push_cast at this
    linarith
  have hPm : |evalR pE (value q1.toBits)| ≤ 1 / 2 ^ 22 := by
    have : ((bnd pE Xq).1 : ℝ) ≤ ((1 / 2 ^ 22 : ℚ) : ℝ) := by exact_mod_cast pE_mag
    push_cast at this
    linarith
  have hflb : |value (evalF pE q1).toBits| ≤ 1 / 2 ^ 21 := by
    have := abs_sub_abs_le_abs_sub (value (evalF pE q1).toBits) (evalR pE (value q1.toBits))
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 22 + 1 / 2 ^ 74 ≤ 1 / 2 ^ 21)]
  -- the constants
  have h128v := ev 128 128 rfl (by norm_num)
  have h129v := ev 129 129 rfl (by norm_num)
  have h128f := ef 128 128 rfl (by norm_num)
  have h129f := ef 129 129 rfl (by norm_num)
  set c128 := (PolyBound.ratOfWord expdTable[128]! : ℝ) with hc128
  set c129 := (PolyBound.ratOfWord expdTable[129]! : ℝ) with hc129
  have hc128lo : 1 / 1480 ≤ c128 := by
    have : ((1 / 1480 : ℚ) : ℝ) ≤ c128 := by rw [hc128]; exact_mod_cast c128_lo
    push_cast at this; exact this
  have hc128hi : c128 ≤ 1 / 1470 := by
    have : c128 ≤ ((1 / 1470 : ℚ) : ℝ) := by rw [hc128]; exact_mod_cast c128_hi
    push_cast at this; exact this
  have hc129b : |c129| ≤ 1 / 2 ^ 65 := by
    have := TgammaSmall.abs_rat_le _ _ c129_le
    push_cast at this; exact this
  -- `a = fastTwoSum c128 fl`
  obtain ⟨ha1f, ha2f, hasum, -, ha2b⟩ := fastTwoSum_spec (entry expdTable 128) (evalF pE q1) h128f
    hfl.1 (by rw [h128v, abs_of_pos (show (0 : ℝ) < c128 by linarith)]
              linarith [(by norm_num : (1 : ℝ) / 2 ^ 21 ≤ 1 / 1480)])
    (by rw [h128v, abs_of_pos (show (0 : ℝ) < c128 by linarith)]
        linarith [(by norm_num : (1 : ℝ) / 1470 < 2 ^ 900)])
  rw [h128v] at hasum
  set a := fastTwoSum (entry expdTable 128) (evalF pE q1) with hadef
  have ha1b : |value a.1.toBits| ≤ 1 / 2 ^ 10 := by
    have h1 := abs_add_le (value a.1.toBits + value a.2.toBits) (-value a.2.toBits)
    rw [add_neg_cancel_right, abs_neg, hasum] at h1
    have h2 := abs_add_le c128 (value (evalF pE q1).toBits)
    rw [abs_of_pos (by linarith : (0 : ℝ) < c128)] at h2
    linarith [(by norm_num : (1 : ℝ) / 1470 + 1 / 2 ^ 21 + (1 / 2 ^ 10 / 2 ^ 52 + 1 / 2 ^ 1074) ≤
      1 / 2 ^ 10)]
  have ha2 : |value a.2.toBits| ≤ 1 / 2 ^ 61 := by
    have : |value a.1.toBits| / 2 ^ 52 ≤ 1 / 2 ^ 10 / 2 ^ 52 :=
      div_le_div_of_nonneg_right ha1b (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 10 / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 61)]
  -- `a2' = a.2 + c129`
  have ha2' := fapprox_add (fapprox_self a.2 ha2f) (fapprox_self _ h129f) (1 / 2 ^ 60)
    (by rw [h129v, add_zero, add_zero]; linarith [abs_add_le (value a.2.toBits) c129,
      (by norm_num : (1 : ℝ) / 2 ^ 61 + 1 / 2 ^ 65 ≤ 1 / 2 ^ 60)])
    (by norm_num)
  rw [h129v] at ha2'
  set a2' := a.2 + entry expdTable 129 with ha2'def
  have ha2'b : |value a2'.toBits| ≤ 1 / 2 ^ 60 := by
    have := abs_sub_abs_le_abs_sub (value a2'.toBits) (value a.2.toBits + c129)
    have h3 := ha2'.2
    linarith [abs_add_le (value a.2.toBits) c129, (by norm_num : (1 : ℝ) / 2 ^ 61 + 1 / 2 ^ 65 +
      (0 + 0 + 1 / 2 ^ 60 / 2 ^ 53) ≤ 1 / 2 ^ 60)]
  -- `b = mulDD q1 q2 a.1 a2'`
  have hq10 := abs_nonneg (value q1.toBits)
  have hq20 := abs_nonneg (value q2.toBits)
  obtain ⟨hb1f, hb2f, -, hb2b, hb1b⟩ := mulDD_spec hF q1 q2 a.1 a2' hq1f hq2f ha1f ha2'.1
    (1 / 2 ^ 10 * 1) (1 / 2 ^ 10 * (1 / 2 ^ 52)) (1 / 2 ^ 60 * 1) (1 / 2 ^ 60 * (1 / 2 ^ 52))
    (mul_le_mul ha1b (by linarith) hq10 (by norm_num))
    (mul_le_mul ha1b hq2 hq20 (by norm_num))
    (mul_le_mul ha2'b (by linarith) hq10 (by norm_num))
    (mul_le_mul ha2'b hq2 hq20 (by norm_num)) (by norm_num) (by norm_num)
  set b := mulDD q1 q2 a.1 a2' with hbdef
  have hb2 : |value b.2.toBits| ≤ 1 / 2 ^ 59 := hb2b.trans (by norm_num)
  have hb1 : |value b.1.toBits| ≤ 1 / 2 ^ 9 := hb1b.trans (by norm_num)
  -- `c = fastTwoSum 1 b.1`: `c.1` is the rounded `1 + b.1`, and `c.2` its rounding error
  obtain ⟨-, hc2f, hcsum, -, -⟩ := fastTwoSum_spec 1.0 b.1 one_finite hb1f
    (by rw [one_value, abs_one]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 9 ≤ 1)])
    (by rw [one_value, abs_one]; norm_num)
  rw [one_value] at hcsum
  have hS1 : 1 - 1 / 2 ^ 9 ≤ |1 + value b.1.toBits| := by
    have := abs_sub_abs_le_abs_sub (1 : ℝ) (-value b.1.toBits)
    rw [sub_neg_eq_add, abs_one, abs_neg] at this
    linarith
  have hS2 : |1 + value b.1.toBits| ≤ 1 + 1 / 2 ^ 9 := by
    have := abs_add_le (1 : ℝ) (value b.1.toBits)
    rw [abs_one] at this
    linarith
  have hr := fapprox_add (fapprox_self 1.0 one_finite) (fapprox_self b.1 hb1f)
    |1 + value b.1.toBits| (by rw [one_value]; simp)
    (by linarith [(by norm_num : (1 : ℝ) + 1 / 2 ^ 9 < 2 ^ 1023)])
  have hc1eq : (fastTwoSum 1.0 b.1).1 = 1.0 + b.1 := rfl
  rw [← hc1eq, one_value] at hr
  have hre := hr.2
  simp only [zero_add] at hre
  set c := fastTwoSum 1.0 b.1 with hcdef
  have hc2 : |value c.2.toBits| ≤ |1 + value b.1.toBits| / 2 ^ 53 := by
    rw [show value c.2.toBits = -(value c.1.toBits - (1 + value b.1.toBits)) by linarith, abs_neg]
    exact hre
  have hc1 : |1 + value b.1.toBits| * (1 - 1 / 2 ^ 53) ≤ |value c.1.toBits| := by
    have := abs_sub_abs_le_abs_sub (1 + value b.1.toBits) (value c.1.toBits)
    rw [abs_sub_comm] at this
    linarith
  -- `e = b.2 + c.2`
  have he := fapprox_add (fapprox_self b.2 hb2f) (fapprox_self c.2 hc2f)
    (1 / 2 ^ 59 + |1 + value b.1.toBits| / 2 ^ 53)
    (by linarith [abs_add_le (value b.2.toBits) (value c.2.toBits)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 59 + (1 + 1 / 2 ^ 9) / 2 ^ 53 < 2 ^ 1023)])
  have hem := Approx.mag he
  have hbc := abs_add_le (value b.2.toBits) (value c.2.toBits)
  refine ⟨by linarith [(by norm_num : (1 - 1 / 2 ^ 9 : ℝ) * (1 - 1 / 2 ^ 53) ≥ 99 / 100)], ?_⟩
  linarith

/-- **The low part of `asExpd`** below `2 ^ -50` of its high part. -/
theorem asExpd_low (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (x l : Float)
    (hx : Finite x.toBits) (hl : Finite l.toBits) (h1 : 1 ≤ value x.toBits + value l.toBits)
    (h2 : value x.toBits + value l.toBits ≤ 1000) (hlb : |value l.toBits| ≤ 1 / 2 ^ 14) :
    |value (asExpd expdTable x l).2.1.toBits| ≤ |value (asExpd expdTable x l).1.toBits| / 2 ^ 50 := by
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
  obtain ⟨K, hKv, hK22, hixf, hq1f, hq2f, -, hq1b, hq2b⟩ :=
    exp_red p1 p2 hp1f hp2f hp2b hp1lo (by linarith [(abs_le.mp hp1b).2])
  rw [toWord_nat (roundEven p1) K hixf hKv.symm (by omega)]
  generalize fastTwoSum (p1 - roundEven p1) p2 = q at hq1f hq2f hq1b hq2b ⊢
  obtain ⟨q1, q2⟩ := q
  dsimp only at hq1f hq2f hq1b hq2b ⊢
  obtain ⟨hi0, hi1, -⟩ := exp_index K (by omega)
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
  obtain ⟨hr1f, hr2f, -, -, hr1b⟩ := exp_table hF _ _ hn0 hn1
  obtain ⟨hr1lo, hrl⟩ := table_low hF _ _ hn0 hn1
  generalize mulDD (Float.ofBits expdTable[2 * (K / 32 % 32) + 1]!)
    (Float.ofBits expdTable[2 * (K / 32 % 32)]!) (Float.ofBits expdTable[64 + 2 * (K % 32) + 1]!)
    (Float.ofBits expdTable[64 + 2 * (K % 32)]!) = r at hr1f hr2f hr1b hr1lo hrl ⊢
  obtain ⟨r1, r2⟩ := r
  dsimp only at hr1f hr2f hr1b hr1lo hrl ⊢
  -- the kernel
  obtain ⟨hc1f, hef, -, hc1b, -⟩ := exp_poly hF q1 q2 hq1f hq2f
    (by linarith [(by norm_num : (61 : ℝ) / 100 ≤ 5 / 8)]) hq2b
  obtain ⟨hc1lo, hel⟩ := kernel_low hF q1 q2 hq1f hq2f
    (by linarith [(by norm_num : (61 : ℝ) / 100 ≤ 5 / 8)]) hq2b
  generalize fastTwoSum (entry expdTable 128) (evalF pE q1) = a at hc1f hef hc1b hc1lo hel ⊢
  obtain ⟨a1, a2⟩ := a
  dsimp only at hc1f hef hc1b hc1lo hel ⊢
  generalize mulDD q1 q2 a1 (a2 + entry expdTable 129) = b at hc1f hef hc1b hc1lo hel ⊢
  obtain ⟨b1, b2⟩ := b
  dsimp only at hc1f hef hc1b hc1lo hel ⊢
  generalize fastTwoSum 1.0 b1 = c at hc1f hef hc1b hc1lo hel ⊢
  obtain ⟨c1, c2⟩ := c
  dsimp only at hc1f hef hc1b hc1lo hel ⊢
  generalize b2 + c2 = e at hef hel ⊢
  -- the final product
  have hr10 := abs_nonneg (value r1.toBits)
  have hc10 := abs_nonneg (value c1.toBits)
  have he0 := abs_nonneg (value e.toBits)
  obtain ⟨-, -, -, hflow, -⟩ := mulDD_spec hF r1 r2 c1 e hr1f hr2f hc1f hef
    (|value c1.toBits| * |value r1.toBits|) (|value c1.toBits| * |value r2.toBits|)
    (|value e.toBits| * |value r1.toBits|) (|value e.toBits| * |value r2.toBits|)
    le_rfl le_rfl le_rfl le_rfl
    (by nlinarith) (by nlinarith [abs_nonneg (value r2.toBits)])
  have hP1 : |value c1.toBits| * |value r2.toBits| ≤
      |value c1.toBits| * |value r1.toBits| * (401 / 100 / 2 ^ 53) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hrl hc10
  have hP2 : |value e.toBits| * |value r1.toBits| ≤
      |value c1.toBits| * |value r1.toBits| * (21 / 20 / 2 ^ 53) := by
    rw [show |value c1.toBits| * |value r1.toBits| * (21 / 20 / 2 ^ 53) =
      |value c1.toBits| * (21 / 20 / 2 ^ 53) * |value r1.toBits| by ring]
    exact mul_le_mul_of_nonneg_right hel hr10
  have hH : 99 / 100 * (1 / 2) ≤ |value c1.toBits| * |value r1.toBits| :=
    mul_le_mul hc1lo hr1lo (by norm_num) hc10
  have hlo := mul_lower c1 r1 hc1f hr1f (by nlinarith)
  have hf1 : (mulDD r1 r2 c1 e).1 = c1 * r1 := rfl
  rw [hf1]
  linarith

#print axioms table_low
#print axioms kernel_low
#print axioms asExpd_low

end Library.Numerics.Float64.Tgamma.TgammaExpLow
