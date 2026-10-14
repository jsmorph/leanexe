import Verified.Examples.TgammaAsym1

/-!
The product `(l - 1)(x - 1/2)` of `Lgamma.asLgammaAsymAccurate`, for the logarithm
`l = l0 + l1 + l2` and `w = wh + wl = x - 1/2` (`prod_spec`).  The code computes
`l0x = (l0 - 1) wh` with its `fma` residual, `l1x = l1 wh` with its residual, and `l2 wh`, adds
the residuals with `sumDD`, and adds `(l0 - 1) wl` and `l1 wl` with a second `sumDD`; it drops
`l2 wl`.  `l0 - 1` and, below `2^52`, `xh - 1/2` are exact (`one_sub_wide`, `half_sub_wide`), by
`TgammaAsym1.sub_exact_binade` on the binade of the minuend (`binade_of`).  The largest error is
the rounding of `(l0 - 1) wl`, at most `83 |wl|/2^53`.
-/

namespace Verified.Examples.LgammaAsymProd
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaAsym1 TgammaRecip

set_option exponentiation.threshold 4096

/-- The binade of a real `x ≥ 1`. -/
theorem binade_of (x : ℝ) (h1 : 1 ≤ x) : ∃ e : ℕ, (2 : ℝ) ^ e ≤ x ∧ x < 2 ^ (e + 1) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊x⌋₊ := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by rw [hn]; exact Nat.le_floor (by exact_mod_cast h1)
  have h3 : (n : ℝ) ≤ x := by rw [hn]; exact Nat.floor_le (by linarith)
  have h4 : x < (n : ℝ) + 1 := by rw [hn]; exact Nat.lt_floor_add_one x
  refine ⟨Nat.log 2 n, ?_, ?_⟩
  · have := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have h2 : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    push_cast at h2
    linarith
  · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have h2 : (n : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 n + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h2
    linarith

/-- `x - 1/2` is exact for `1 ≤ x < 2^52`. -/
theorem half_sub_wide (x : Float) (hx : Finite x.toBits) (h1 : 1 ≤ value x.toBits)
    (h2 : value x.toBits < 2 ^ 52) :
    Finite (x - 0.5).toBits ∧ value (x - 0.5).toBits = value x.toBits - 1 / 2 := by
  obtain ⟨e, hlo, hhi⟩ := binade_of _ h1
  have he : e ≤ 51 := by
    by_contra h
    have : (2 : ℝ) ^ 52 ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  rw [← TgammaTiny.half_value]
  refine sub_exact_binade x 0.5 hx TgammaTiny.half_finite e (by omega) hlo hhi
    (by rw [TgammaTiny.half_value]; norm_num) (by rw [TgammaTiny.half_value]; linarith)
    (2 ^ (51 - e)) ?_
  rw [TgammaTiny.half_value]
  push_cast
  rw [show (1 : ℝ) / 2 * 2 ^ 1074 = 2 ^ 1073 by norm_num, ← pow_add]
  congr 1
  omega

/-- `x - 1` is exact for `1 ≤ x < 2^52`. -/
theorem one_sub_wide (x : Float) (hx : Finite x.toBits) (h1 : 1 ≤ value x.toBits)
    (h2 : value x.toBits < 2 ^ 52) :
    Finite (x - 1.0).toBits ∧ value (x - 1.0).toBits = value x.toBits - 1 := by
  obtain ⟨e, hlo, hhi⟩ := binade_of _ h1
  have he : e ≤ 51 := by
    by_contra h
    have : (2 : ℝ) ^ 52 ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  rw [← one_value]
  refine sub_exact_binade x 1.0 hx one_finite e (by omega) hlo hhi (by rw [one_value]; norm_num)
    (by rw [one_value]; linarith) (2 ^ (52 - e)) ?_
  rw [one_value]
  push_cast
  rw [one_mul, ← pow_add]
  congr 1
  omega

/-- The code of the product. -/
def prodCode (l0 l1 l2 wh wl : Float) : Float × Float × Float :=
  let l0m := l0 - 1.0
  let l0x := l0m * wh
  let l0xl := Fma.fma l0m wh (-l0x)
  let l1x := l1 * wh
  let l1xl := Fma.fma l1 wh (-l1x)
  let l2x := l2 * wh
  let s := sumDD l1x l2x l0xl l1xl
  let s' := sumDD s.1 s.2 (l0m * wl) (l1 * wl)
  (l0x, s'.1, s'.2)

set_option maxHeartbeats 4000000 in
/-- **The product** `(l - 1)(x - 1/2)` within `wh/2^95`. -/
theorem prod_spec (hF : FmaSpec.FmaNearest) (l0 l1 l2 wh wl : Float) (h0f : Finite l0.toBits)
    (h1f : Finite l1.toBits) (h2f : Finite l2.toBits) (hwf : Finite wh.toBits)
    (hlf : Finite wl.toBits) (hl0lo : 1 ≤ value l0.toBits) (hl0hi : value l0.toBits ≤ 84)
    (hl1 : |value l1.toBits| ≤ |value l0.toBits| / 2 ^ 50 + 1 / 2 ^ 49)
    (hl2 : |value l2.toBits| ≤ |value l0.toBits| / 2 ^ 99 + 1 / 2 ^ 98)
    (hwlo : 1 ≤ value wh.toBits) (hwhi : value wh.toBits ≤ 2 ^ 801)
    (hwl : |value wl.toBits| ≤ value wh.toBits / 2 ^ 50) :
    let P := prodCode l0 l1 l2 wh wl
    Finite P.1.toBits ∧ Finite P.2.1.toBits ∧ Finite P.2.2.toBits ∧
      |value P.1.toBits + value P.2.1.toBits + value P.2.2.toBits -
          (value l0.toBits + value l1.toBits + value l2.toBits - 1) *
            (value wh.toBits + value wl.toBits)| ≤ value wh.toBits / 2 ^ 95 ∧
      |value P.1.toBits - (value l0.toBits - 1) * value wh.toBits| ≤
        84 * value wh.toBits / 2 ^ 53 ∧
      |value P.2.1.toBits| ≤ value wh.toBits / 2 ^ 40 ∧
      |value P.2.2.toBits| ≤ value wh.toBits / 2 ^ 86 := by
  intro P
  set W := value wh.toBits with hWdef
  set a0 := value l0.toBits with ha0
  set a1 := value l1.toBits with ha1
  set a2 := value l2.toBits with ha2
  set b := value wl.toBits with hbdef
  have hW0 : 0 < W := by linarith
  have ha0' : |a0| ≤ 84 := abs_le.mpr ⟨by linarith, hl0hi⟩
  have ha1b : |a1| ≤ 1 / 2 ^ 43 := by
    have : |a0| / 2 ^ 50 ≤ 84 / 2 ^ 50 := div_le_div_of_nonneg_right ha0' (by norm_num)
    linarith [(by norm_num : (84 : ℝ) / 2 ^ 50 + 1 / 2 ^ 49 ≤ 1 / 2 ^ 43)]
  have ha2b : |a2| ≤ 1 / 2 ^ 92 := by
    have : |a0| / 2 ^ 99 ≤ 84 / 2 ^ 99 := div_le_div_of_nonneg_right ha0' (by norm_num)
    linarith [(by norm_num : (84 : ℝ) / 2 ^ 99 + 1 / 2 ^ 98 ≤ 1 / 2 ^ 92)]
  -- `l0m = l0 - 1`, exact
  obtain ⟨hmf, hmv⟩ := one_sub_wide l0 h0f hl0lo (by linarith)
  set l0m := l0 - 1.0 with hl0m
  have hm0 : 0 ≤ value l0m.toBits := by rw [hmv]; linarith
  have hm83 : value l0m.toBits ≤ 83 := by rw [hmv]; linarith
  have hmabs : |value l0m.toBits| ≤ 83 := abs_le.mpr ⟨by linarith, hm83⟩
  have hWabs : |W| ≤ W := le_of_eq (abs_of_pos hW0)
  have hWmax : W ≤ 2 ^ 801 := hwhi
  -- `l0x = l0m wh` and its residual
  have hx0 := fapprox_mul (fapprox_self l0m hmf) (fapprox_self wh hwf) 83 W hmabs hWabs (83 * W)
    (by simp only [add_zero]; exact le_rfl) (by linarith [(by norm_num : (83 : ℝ) * 2 ^ 801 < 2 ^ 1022)])
  simp only [mul_zero, zero_mul, add_zero, zero_add] at hx0
  set l0x := l0m * wh with hl0x
  have hx0b : |value l0x.toBits| ≤ 84 * W := by
    have := hx0.2
    have h1 := abs_sub_abs_le_abs_sub (value l0x.toBits) (value l0m.toBits * W)
    have h2 : |value l0m.toBits * W| ≤ 83 * W := by
      rw [abs_mul, abs_of_pos hW0]; exact mul_le_mul_of_nonneg_right hmabs hW0.le
    have h3 : (1 : ℝ) / 2 ^ 1075 ≤ W := by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1)]
    linarith
  have hnx0 := fapprox_neg (fapprox_self l0x hx0.1)
  have hnx0v : value (-l0x).toBits = -value l0x.toBits := by
    have h0 := abs_nonpos_iff.mp hnx0.2
    linarith
  have hr0 := fma_approx hF l0m wh (-l0x) hmf hwf hnx0.1 (by
    rw [hnx0v, ← sub_eq_add_neg]
    have := hx0.2
    have : 83 * W / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 2 ^ 1000 := by
      linarith [(by norm_num : (83 : ℝ) * 2 ^ 801 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 2 ^ 1000),
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwhi (by norm_num : (0 : ℝ) ≤ 83))
          (by norm_num : (0 : ℝ) ≤ 2 ^ 53)]
    linarith [abs_sub_comm (value l0m.toBits * value wh.toBits) (value l0x.toBits)])
  rw [hnx0v, ← sub_eq_add_neg] at hr0
  set l0xl := Fma.fma l0m wh (-l0x) with hl0xl
  -- `l1x = l1 wh` and its residual
  have hx1 := fapprox_mul (fapprox_self l1 h1f) (fapprox_self wh hwf) (1 / 2 ^ 43) W ha1b hWabs
    (1 / 2 ^ 43 * W) (by simp only [add_zero]; exact le_rfl)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 43 * 2 ^ 801 < 2 ^ 1022),
      mul_le_mul_of_nonneg_left hwhi (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 43)])
  simp only [mul_zero, zero_mul, add_zero, zero_add] at hx1
  set l1x := l1 * wh with hl1x
  have hx1b : |value l1x.toBits| ≤ W / 2 ^ 42 := by
    have := hx1.2
    have h1 := abs_sub_abs_le_abs_sub (value l1x.toBits) (a1 * W)
    have h2 : |a1 * W| ≤ 1 / 2 ^ 43 * W := by
      rw [abs_mul, abs_of_pos hW0]; exact mul_le_mul_of_nonneg_right ha1b hW0.le
    have h3 : (1 : ℝ) / 2 ^ 1075 ≤ W / 2 ^ 100 := by
      have := div_le_div_of_nonneg_right hwlo (by norm_num : (0 : ℝ) ≤ 2 ^ 100)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 100)]
    linarith [(by ring : W / 2 ^ 42 = 1 / 2 ^ 43 * W + 1 / 2 ^ 43 * W)]
  have hnx1 := fapprox_neg (fapprox_self l1x hx1.1)
  have hnx1v : value (-l1x).toBits = -value l1x.toBits := by
    have h0 := abs_nonpos_iff.mp hnx1.2
    linarith
  have hr1 := fma_approx hF l1 wh (-l1x) h1f hwf hnx1.1 (by
    rw [hnx1v, ← sub_eq_add_neg]
    have := hx1.2
    have : 1 / 2 ^ 43 * W / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 2 ^ 1000 := by
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 43 * 2 ^ 801 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 2 ^ 1000),
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwhi (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 43))
          (by norm_num : (0 : ℝ) ≤ 2 ^ 53)]
    linarith [abs_sub_comm (value l1.toBits * value wh.toBits) (value l1x.toBits)])
  rw [hnx1v, ← sub_eq_add_neg] at hr1
  set l1xl := Fma.fma l1 wh (-l1x) with hl1xl
  -- `l2x = l2 wh`
  have hx2 := fapprox_mul (fapprox_self l2 h2f) (fapprox_self wh hwf) (1 / 2 ^ 92) W ha2b hWabs
    (1 / 2 ^ 92 * W) (by simp only [add_zero]; exact le_rfl)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 92 * 2 ^ 801 < 2 ^ 1022),
      mul_le_mul_of_nonneg_left hwhi (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 92)])
  simp only [mul_zero, zero_mul, add_zero, zero_add] at hx2
  set l2x := l2 * wh with hl2x
  -- the small terms, relative to `W`
  have hη : (1 : ℝ) / 2 ^ 1075 ≤ W / 2 ^ 1000 := by
    have := div_le_div_of_nonneg_right hwlo (by norm_num : (0 : ℝ) ≤ 2 ^ 1000)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000)]
  have hr0b : |value l0xl.toBits - (value l0m.toBits * W - value l0x.toBits)| ≤ W / 2 ^ 99 := by
    have h1 := hr0.2
    have h2 : |value l0m.toBits * W - value l0x.toBits| ≤ 83 * W / 2 ^ 53 + 1 / 2 ^ 1075 := by
      rw [abs_sub_comm]; exact hx0.2
    have h3 : |value l0m.toBits * W - value l0x.toBits| / 2 ^ 53 ≤
        (83 * W / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 := div_le_div_of_nonneg_right h2 (by norm_num)
    have h4 : (83 * W / 2 ^ 53 + W / 2 ^ 1000) / 2 ^ 53 + W / 2 ^ 1000 ≤ W / 2 ^ 99 := by
      have : (83 * W / 2 ^ 53 + W / 2 ^ 1000) / 2 ^ 53 + W / 2 ^ 1000 =
          W * ((83 / 2 ^ 53 + 1 / 2 ^ 1000) / 2 ^ 53 + 1 / 2 ^ 1000) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : ((83 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1000) / 2 ^ 53 +
        1 / 2 ^ 1000 ≤ 1 / 2 ^ 99) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 99) = W / 2 ^ 99)]
    linarith
  have hr1b : |value l1xl.toBits - (a1 * W - value l1x.toBits)| ≤ W / 2 ^ 140 := by
    have h1 := hr1.2
    have h2 : |a1 * W - value l1x.toBits| ≤ 1 / 2 ^ 43 * W / 2 ^ 53 + 1 / 2 ^ 1075 := by
      rw [abs_sub_comm]; exact hx1.2
    have h3 : |a1 * W - value l1x.toBits| / 2 ^ 53 ≤
        (1 / 2 ^ 43 * W / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 := div_le_div_of_nonneg_right h2 (by norm_num)
    have h4 : (1 / 2 ^ 43 * W / 2 ^ 53 + W / 2 ^ 1000) / 2 ^ 53 + W / 2 ^ 1000 ≤ W / 2 ^ 140 := by
      have : (1 / 2 ^ 43 * W / 2 ^ 53 + W / 2 ^ 1000) / 2 ^ 53 + W / 2 ^ 1000 =
          W * ((1 / 2 ^ 43 / 2 ^ 53 + 1 / 2 ^ 1000) / 2 ^ 53 + 1 / 2 ^ 1000) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : ((1 : ℝ) / 2 ^ 43 / 2 ^ 53 + 1 / 2 ^ 1000) /
        2 ^ 53 + 1 / 2 ^ 1000 ≤ 1 / 2 ^ 140) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 140) = W / 2 ^ 140)]
    linarith
  have hl1xlb : |value l1xl.toBits| ≤ W / 2 ^ 95 := by
    have h1 := abs_sub_abs_le_abs_sub (value l1xl.toBits) (a1 * W - value l1x.toBits)
    have h2 : |a1 * W - value l1x.toBits| ≤ 1 / 2 ^ 43 * W / 2 ^ 53 + 1 / 2 ^ 1075 := by
      rw [abs_sub_comm]; exact hx1.2
    have : 1 / 2 ^ 43 * W / 2 ^ 53 + W / 2 ^ 1000 + W / 2 ^ 140 ≤ W / 2 ^ 95 := by
      have : 1 / 2 ^ 43 * W / 2 ^ 53 + W / 2 ^ 1000 + W / 2 ^ 140 =
          W * (1 / 2 ^ 43 / 2 ^ 53 + 1 / 2 ^ 1000 + 1 / 2 ^ 140) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 43 / 2 ^ 53 + 1 / 2 ^ 1000 +
        1 / 2 ^ 140 ≤ 1 / 2 ^ 95) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 95) = W / 2 ^ 95)]
    linarith
  have hl0xlb : |value l0xl.toBits| ≤ W / 2 ^ 45 := by
    have h1 := abs_sub_abs_le_abs_sub (value l0xl.toBits) (value l0m.toBits * W - value l0x.toBits)
    have h2 : |value l0m.toBits * W - value l0x.toBits| ≤ 83 * W / 2 ^ 53 + 1 / 2 ^ 1075 := by
      rw [abs_sub_comm]; exact hx0.2
    have : 83 * W / 2 ^ 53 + W / 2 ^ 1000 + W / 2 ^ 99 ≤ W / 2 ^ 45 := by
      have : 83 * W / 2 ^ 53 + W / 2 ^ 1000 + W / 2 ^ 99 =
          W * (83 / 2 ^ 53 + 1 / 2 ^ 1000 + 1 / 2 ^ 99) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (83 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1000 +
        1 / 2 ^ 99 ≤ 1 / 2 ^ 45) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 45) = W / 2 ^ 45)]
    linarith
  have hl2xb : |value l2x.toBits| ≤ W / 2 ^ 91 := by
    have h1 := abs_sub_abs_le_abs_sub (value l2x.toBits) (a2 * W)
    have h2 : |a2 * W| ≤ 1 / 2 ^ 92 * W := by
      rw [abs_mul, abs_of_pos hW0]; exact mul_le_mul_of_nonneg_right ha2b hW0.le
    have h3 := hx2.2
    have : 1 / 2 ^ 92 * W + (1 / 2 ^ 92 * W / 2 ^ 53 + W / 2 ^ 1000) ≤ W / 2 ^ 91 := by
      have : 1 / 2 ^ 92 * W + (1 / 2 ^ 92 * W / 2 ^ 53 + W / 2 ^ 1000) =
          W * (1 / 2 ^ 92 + (1 / 2 ^ 92 / 2 ^ 53 + 1 / 2 ^ 1000)) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 92 + (1 / 2 ^ 92 / 2 ^ 53 +
        1 / 2 ^ 1000) ≤ 1 / 2 ^ 91) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 91) = W / 2 ^ 91)]
    linarith
  -- the first `sumDD`
  have hlimA : |value l1x.toBits| < 2 ^ 898 := by
    have : W / 2 ^ 42 ≤ 2 ^ 801 / 2 ^ 42 := div_le_div_of_nonneg_right hwhi (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 801 / 2 ^ 42 < 2 ^ 898)]
  have hlimB : |value l0xl.toBits| < 2 ^ 898 := by
    have : W / 2 ^ 45 ≤ 2 ^ 801 / 2 ^ 45 := div_le_div_of_nonneg_right hwhi (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 801 / 2 ^ 45 < 2 ^ 898)]
  have hLA : |value l2x.toBits| + |value l1xl.toBits| ≤ W / 2 ^ 90 := by
    linarith [(by ring : W / 2 ^ 90 = W / 2 ^ 91 + W / 2 ^ 91),
      div_le_div_of_nonneg_left hW0.le (by norm_num : (0 : ℝ) < 2 ^ 91) (by norm_num :
        (2 : ℝ) ^ 91 ≤ 2 ^ 95)]
  obtain ⟨sAf, sBf, sE, sB2, sB1⟩ := sumDD_spec l1x l2x l0xl l1xl hx1.1 hx2.1 hr0.1 hr1.1 hlimA hlimB
    (W / 2 ^ 90) hLA (by
      have : W / 2 ^ 90 ≤ 2 ^ 801 / 2 ^ 90 := div_le_div_of_nonneg_right hwhi (by norm_num)
      linarith [(by norm_num : (2 : ℝ) ^ 801 / 2 ^ 90 ≤ 2 ^ 800)])
  set s := sumDD l1x l2x l0xl l1xl with hsdef
  have hs1b : |value s.1.toBits| ≤ W / 2 ^ 41 := by
    have h1 := abs_add_le (value l1x.toBits) (value l0xl.toBits)
    have h2 := mul_le_mul_of_nonneg_right (show |value l1x.toBits + value l0xl.toBits| ≤
      W / 2 ^ 42 + W / 2 ^ 45 by linarith) (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    have : (W / 2 ^ 42 + W / 2 ^ 45) * (1 + 1 / 2 ^ 51) + W / 2 ^ 1000 ≤ W / 2 ^ 41 := by
      have : (W / 2 ^ 42 + W / 2 ^ 45) * (1 + 1 / 2 ^ 51) + W / 2 ^ 1000 =
          W * ((1 / 2 ^ 42 + 1 / 2 ^ 45) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1000) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : ((1 : ℝ) / 2 ^ 42 + 1 / 2 ^ 45) *
        (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1000 ≤ 1 / 2 ^ 41) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 41) = W / 2 ^ 41)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1073 ≤ 1 / 2 ^ 1075 * 4), hη]
  have hs2b : |value s.2.toBits| ≤ W / 2 ^ 88 := by
    have h1 : |value s.1.toBits| / 2 ^ 51 ≤ W / 2 ^ 41 / 2 ^ 51 :=
      div_le_div_of_nonneg_right hs1b (by norm_num)
    have : W / 2 ^ 90 * (1 + 1 / 2 ^ 51) + W / 2 ^ 41 / 2 ^ 51 + W / 2 ^ 1000 ≤ W / 2 ^ 88 := by
      have : W / 2 ^ 90 * (1 + 1 / 2 ^ 51) + W / 2 ^ 41 / 2 ^ 51 + W / 2 ^ 1000 =
          W * (1 / 2 ^ 90 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 41 / 2 ^ 51 + 1 / 2 ^ 1000) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 90 * (1 + 1 / 2 ^ 51) +
        1 / 2 ^ 41 / 2 ^ 51 + 1 / 2 ^ 1000 ≤ 1 / 2 ^ 88) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 88) = W / 2 ^ 88)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1073 ≤ 1 / 2 ^ 1075 * 4), hη]
  have hsE : |value s.1.toBits + value s.2.toBits -
      (value l1x.toBits + value l2x.toBits + (value l0xl.toBits + value l1xl.toBits))| ≤
      W / 2 ^ 140 := by
    have h1 : |value s.1.toBits| / 2 ^ 52 ≤ W / 2 ^ 41 / 2 ^ 52 :=
      div_le_div_of_nonneg_right hs1b (by norm_num)
    have : (3 * (W / 2 ^ 90) + W / 2 ^ 41 / 2 ^ 52 + W / 2 ^ 1000) / 2 ^ 53 ≤ W / 2 ^ 140 := by
      have : (3 * (W / 2 ^ 90) + W / 2 ^ 41 / 2 ^ 52 + W / 2 ^ 1000) / 2 ^ 53 =
          W * ((3 / 2 ^ 90 + 1 / 2 ^ 41 / 2 ^ 52 + 1 / 2 ^ 1000) / 2 ^ 53) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : ((3 : ℝ) / 2 ^ 90 + 1 / 2 ^ 41 / 2 ^ 52 +
        1 / 2 ^ 1000) / 2 ^ 53 ≤ 1 / 2 ^ 140) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 140) = W / 2 ^ 140)]
    have h2 : (3 * (W / 2 ^ 90) + |value s.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ≤
        (3 * (W / 2 ^ 90) + W / 2 ^ 41 / 2 ^ 52 + W / 2 ^ 1000) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 1 / 2 ^ 1075 * 2)])
        (by norm_num)
    linarith
  -- `p0 = l0m wl`, `p1 = l1 wl`
  have hbW : |b| ≤ W / 2 ^ 50 := hwl
  have hp0 := fapprox_mul (fapprox_self l0m hmf) (fapprox_self wl hlf) 83 (W / 2 ^ 50) hmabs hbW
    (83 * (W / 2 ^ 50)) (by simp only [add_zero]; exact le_rfl)
    (by
      have : 83 * (W / 2 ^ 50) ≤ 83 * (2 ^ 801 / 2 ^ 50) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hwhi (by norm_num)) (by norm_num)
      linarith [(by norm_num : (83 : ℝ) * (2 ^ 801 / 2 ^ 50) < 2 ^ 1022)])
  simp only [mul_zero, zero_mul, add_zero, zero_add] at hp0
  have hp1 := fapprox_mul (fapprox_self l1 h1f) (fapprox_self wl hlf) (1 / 2 ^ 43) (W / 2 ^ 50) ha1b
    hbW (1 / 2 ^ 43 * (W / 2 ^ 50)) (by simp only [add_zero]; exact le_rfl)
    (by
      have : 1 / 2 ^ 43 * (W / 2 ^ 50) ≤ 1 / 2 ^ 43 * (2 ^ 801 / 2 ^ 50) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hwhi (by norm_num)) (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 43 * (2 ^ 801 / 2 ^ 50) < 2 ^ 1022)])
  simp only [mul_zero, zero_mul, add_zero, zero_add] at hp1
  set p0 := l0m * wl with hp0def
  set p1 := l1 * wl with hp1def
  have hp0b : |value p0.toBits| ≤ W / 2 ^ 43 := by
    have h1 := abs_sub_abs_le_abs_sub (value p0.toBits) (value l0m.toBits * b)
    have h2 : |value l0m.toBits * b| ≤ 83 * (W / 2 ^ 50) := by
      rw [abs_mul]; exact mul_le_mul hmabs hbW (abs_nonneg _) (by norm_num)
    have h3 := hp0.2
    have : 83 * (W / 2 ^ 50) + (83 * (W / 2 ^ 50) / 2 ^ 53 + W / 2 ^ 1000) ≤ W / 2 ^ 43 := by
      have : 83 * (W / 2 ^ 50) + (83 * (W / 2 ^ 50) / 2 ^ 53 + W / 2 ^ 1000) =
          W * (83 / 2 ^ 50 + (83 / 2 ^ 50 / 2 ^ 53 + 1 / 2 ^ 1000)) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (83 : ℝ) / 2 ^ 50 + (83 / 2 ^ 50 / 2 ^ 53 +
        1 / 2 ^ 1000) ≤ 1 / 2 ^ 43) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 43) = W / 2 ^ 43)]
    linarith
  have hp1b : |value p1.toBits| ≤ W / 2 ^ 92 := by
    have h1 := abs_sub_abs_le_abs_sub (value p1.toBits) (a1 * b)
    have h2 : |a1 * b| ≤ 1 / 2 ^ 43 * (W / 2 ^ 50) := by
      rw [abs_mul]; exact mul_le_mul ha1b hbW (abs_nonneg _) (by norm_num)
    have h3 := hp1.2
    have : 1 / 2 ^ 43 * (W / 2 ^ 50) + (1 / 2 ^ 43 * (W / 2 ^ 50) / 2 ^ 53 + W / 2 ^ 1000) ≤
        W / 2 ^ 92 := by
      have : 1 / 2 ^ 43 * (W / 2 ^ 50) + (1 / 2 ^ 43 * (W / 2 ^ 50) / 2 ^ 53 + W / 2 ^ 1000) =
          W * (1 / 2 ^ 43 / 2 ^ 50 + (1 / 2 ^ 43 / 2 ^ 50 / 2 ^ 53 + 1 / 2 ^ 1000)) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 43 / 2 ^ 50 +
        (1 / 2 ^ 43 / 2 ^ 50 / 2 ^ 53 + 1 / 2 ^ 1000) ≤ 1 / 2 ^ 92) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 92) = W / 2 ^ 92)]
    linarith
  -- the second `sumDD`
  have hlimC : |value s.1.toBits| < 2 ^ 898 := by
    have : W / 2 ^ 41 ≤ 2 ^ 801 / 2 ^ 41 := div_le_div_of_nonneg_right hwhi (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 801 / 2 ^ 41 < 2 ^ 898)]
  have hlimD : |value p0.toBits| < 2 ^ 898 := by
    have : W / 2 ^ 43 ≤ 2 ^ 801 / 2 ^ 43 := div_le_div_of_nonneg_right hwhi (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 801 / 2 ^ 43 < 2 ^ 898)]
  have hLB : |value s.2.toBits| + |value p1.toBits| ≤ W / 2 ^ 87 := by
    have : W / 2 ^ 92 ≤ W / 2 ^ 88 := div_le_div_of_nonneg_left hW0.le (by norm_num) (by norm_num)
    linarith [(by ring : W / 2 ^ 87 = W / 2 ^ 88 + W / 2 ^ 88)]
  obtain ⟨tAf, tBf, tE, tB2, tB1⟩ := sumDD_spec s.1 s.2 p0 p1 sAf sBf hp0.1 hp1.1 hlimC hlimD
    (W / 2 ^ 87) hLB (by
      have : W / 2 ^ 87 ≤ 2 ^ 801 / 2 ^ 87 := div_le_div_of_nonneg_right hwhi (by norm_num)
      linarith [(by norm_num : (2 : ℝ) ^ 801 / 2 ^ 87 ≤ 2 ^ 800)])
  have hP : P = (l0x, (sumDD s.1 s.2 p0 p1).1, (sumDD s.1 s.2 p0 p1).2) := rfl
  simp only [hP]
  set t1 := value (sumDD s.1 s.2 p0 p1).1.toBits with ht1
  set t2 := value (sumDD s.1 s.2 p0 p1).2.toBits with ht2
  have ht1b : |t1| ≤ W / 2 ^ 40 := by
    have h1 := abs_add_le (value s.1.toBits) (value p0.toBits)
    have h2 := mul_le_mul_of_nonneg_right (show |value s.1.toBits + value p0.toBits| ≤
      W / 2 ^ 41 + W / 2 ^ 43 by linarith) (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    have : (W / 2 ^ 41 + W / 2 ^ 43) * (1 + 1 / 2 ^ 51) + W / 2 ^ 1000 ≤ W / 2 ^ 40 := by
      have : (W / 2 ^ 41 + W / 2 ^ 43) * (1 + 1 / 2 ^ 51) + W / 2 ^ 1000 =
          W * ((1 / 2 ^ 41 + 1 / 2 ^ 43) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1000) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : ((1 : ℝ) / 2 ^ 41 + 1 / 2 ^ 43) *
        (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1000 ≤ 1 / 2 ^ 40) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 40) = W / 2 ^ 40)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1073 ≤ 1 / 2 ^ 1075 * 4), hη]
  refine ⟨hx0.1, tAf, tBf, ?_, ?_, ht1b, ?_⟩
  · -- the error
    have hm1 : a0 + a1 + a2 - 1 = value l0m.toBits + a1 + a2 := by rw [hmv]; ring
    have hid : value l0x.toBits + t1 + t2 - (value l0m.toBits + a1 + a2) * (W + b) =
        (t1 + t2 - (value s.1.toBits + value s.2.toBits + (value p0.toBits + value p1.toBits))) +
        (value s.1.toBits + value s.2.toBits -
          (value l1x.toBits + value l2x.toBits + (value l0xl.toBits + value l1xl.toBits))) +
        (value l0xl.toBits - (value l0m.toBits * W - value l0x.toBits)) +
        (value l1xl.toBits - (a1 * W - value l1x.toBits)) +
        (value l2x.toBits - a2 * W) + (value p0.toBits - value l0m.toBits * b) +
        (value p1.toBits - a1 * b) - a2 * b := by ring
    rw [hm1, hid]
    have e1 : |t1 + t2 - (value s.1.toBits + value s.2.toBits + (value p0.toBits + value p1.toBits))| ≤
        W / 2 ^ 130 := by
      have h1 : |t1| / 2 ^ 52 ≤ W / 2 ^ 40 / 2 ^ 52 := div_le_div_of_nonneg_right ht1b (by norm_num)
      have h2 : (3 * (W / 2 ^ 87) + |t1| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ≤
          (3 * (W / 2 ^ 87) + W / 2 ^ 40 / 2 ^ 52 + W / 2 ^ 1000) / 2 ^ 53 :=
        div_le_div_of_nonneg_right (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 1 / 2 ^ 1075 * 2)])
          (by norm_num)
      have : (3 * (W / 2 ^ 87) + W / 2 ^ 40 / 2 ^ 52 + W / 2 ^ 1000) / 2 ^ 53 ≤ W / 2 ^ 130 := by
        have : (3 * (W / 2 ^ 87) + W / 2 ^ 40 / 2 ^ 52 + W / 2 ^ 1000) / 2 ^ 53 =
            W * ((3 / 2 ^ 87 + 1 / 2 ^ 40 / 2 ^ 52 + 1 / 2 ^ 1000) / 2 ^ 53) := by ring
        rw [this]
        have := mul_le_mul_of_nonneg_left (by norm_num : ((3 : ℝ) / 2 ^ 87 + 1 / 2 ^ 40 / 2 ^ 52 +
          1 / 2 ^ 1000) / 2 ^ 53 ≤ 1 / 2 ^ 130) hW0.le
        linarith [(by ring : W * (1 / 2 ^ 130) = W / 2 ^ 130)]
      linarith
    have e5 : |value l2x.toBits - a2 * W| ≤ W / 2 ^ 140 := by
      have h := hx2.2
      have : 1 / 2 ^ 92 * W / 2 ^ 53 + W / 2 ^ 1000 ≤ W / 2 ^ 140 := by
        have : 1 / 2 ^ 92 * W / 2 ^ 53 + W / 2 ^ 1000 = W * (1 / 2 ^ 92 / 2 ^ 53 + 1 / 2 ^ 1000) := by
          ring
        rw [this]
        have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 92 / 2 ^ 53 + 1 / 2 ^ 1000 ≤
          1 / 2 ^ 140) hW0.le
        linarith [(by ring : W * (1 / 2 ^ 140) = W / 2 ^ 140)]
      linarith
    have e6 : |value p0.toBits - value l0m.toBits * b| ≤ W / 2 ^ 96 := by
      have h := hp0.2
      have : 83 * (W / 2 ^ 50) / 2 ^ 53 + W / 2 ^ 1000 ≤ W / 2 ^ 96 := by
        have : 83 * (W / 2 ^ 50) / 2 ^ 53 + W / 2 ^ 1000 = W * (83 / 2 ^ 50 / 2 ^ 53 + 1 / 2 ^ 1000) := by
          ring
        rw [this]
        have := mul_le_mul_of_nonneg_left (by norm_num : (83 : ℝ) / 2 ^ 50 / 2 ^ 53 + 1 / 2 ^ 1000 ≤
          1 / 2 ^ 96) hW0.le
        linarith [(by ring : W * (1 / 2 ^ 96) = W / 2 ^ 96)]
      linarith
    have e7 : |value p1.toBits - a1 * b| ≤ W / 2 ^ 140 := by
      have h := hp1.2
      have : 1 / 2 ^ 43 * (W / 2 ^ 50) / 2 ^ 53 + W / 2 ^ 1000 ≤ W / 2 ^ 140 := by
        have : 1 / 2 ^ 43 * (W / 2 ^ 50) / 2 ^ 53 + W / 2 ^ 1000 =
            W * (1 / 2 ^ 43 / 2 ^ 50 / 2 ^ 53 + 1 / 2 ^ 1000) := by ring
        rw [this]
        have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 43 / 2 ^ 50 / 2 ^ 53 +
          1 / 2 ^ 1000 ≤ 1 / 2 ^ 140) hW0.le
        linarith [(by ring : W * (1 / 2 ^ 140) = W / 2 ^ 140)]
      linarith
    have e8 : |a2 * b| ≤ W / 2 ^ 140 := by
      rw [abs_mul]
      have := mul_le_mul ha2b hbW (abs_nonneg _) (by norm_num)
      have : 1 / 2 ^ 92 * (W / 2 ^ 50) ≤ W / 2 ^ 140 := by
        have : 1 / 2 ^ 92 * (W / 2 ^ 50) = W * (1 / 2 ^ 142) := by ring
        rw [this]
        have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 142 ≤ 1 / 2 ^ 140) hW0.le
        linarith [(by ring : W * (1 / 2 ^ 140) = W / 2 ^ 140)]
      linarith
    have tot : W / 2 ^ 130 + W / 2 ^ 140 + W / 2 ^ 99 + W / 2 ^ 140 + W / 2 ^ 140 + W / 2 ^ 96 +
        W / 2 ^ 140 + W / 2 ^ 140 ≤ W / 2 ^ 95 := by
      have : W / 2 ^ 130 + W / 2 ^ 140 + W / 2 ^ 99 + W / 2 ^ 140 + W / 2 ^ 140 + W / 2 ^ 96 +
          W / 2 ^ 140 + W / 2 ^ 140 = W * (1 / 2 ^ 130 + 5 / 2 ^ 140 + 1 / 2 ^ 99 + 1 / 2 ^ 96) := by
        ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 130 + 5 / 2 ^ 140 + 1 / 2 ^ 99 +
        1 / 2 ^ 96 ≤ 1 / 2 ^ 95) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 95) = W / 2 ^ 95)]
    have a1' := abs_add_le
      ((t1 + t2 - (value s.1.toBits + value s.2.toBits + (value p0.toBits + value p1.toBits))) +
        (value s.1.toBits + value s.2.toBits -
          (value l1x.toBits + value l2x.toBits + (value l0xl.toBits + value l1xl.toBits))) +
        (value l0xl.toBits - (value l0m.toBits * W - value l0x.toBits)) +
        (value l1xl.toBits - (a1 * W - value l1x.toBits)) +
        (value l2x.toBits - a2 * W) + (value p0.toBits - value l0m.toBits * b) +
        (value p1.toBits - a1 * b)) (-(a2 * b))
    rw [← sub_eq_add_neg, abs_neg] at a1'
    have a2' := abs_add_le
      ((t1 + t2 - (value s.1.toBits + value s.2.toBits + (value p0.toBits + value p1.toBits))) +
        (value s.1.toBits + value s.2.toBits -
          (value l1x.toBits + value l2x.toBits + (value l0xl.toBits + value l1xl.toBits))) +
        (value l0xl.toBits - (value l0m.toBits * W - value l0x.toBits)) +
        (value l1xl.toBits - (a1 * W - value l1x.toBits)) +
        (value l2x.toBits - a2 * W) + (value p0.toBits - value l0m.toBits * b))
      (value p1.toBits - a1 * b)
    have a3 := abs_add_le
      ((t1 + t2 - (value s.1.toBits + value s.2.toBits + (value p0.toBits + value p1.toBits))) +
        (value s.1.toBits + value s.2.toBits -
          (value l1x.toBits + value l2x.toBits + (value l0xl.toBits + value l1xl.toBits))) +
        (value l0xl.toBits - (value l0m.toBits * W - value l0x.toBits)) +
        (value l1xl.toBits - (a1 * W - value l1x.toBits)) +
        (value l2x.toBits - a2 * W)) (value p0.toBits - value l0m.toBits * b)
    have a4 := abs_add_le
      ((t1 + t2 - (value s.1.toBits + value s.2.toBits + (value p0.toBits + value p1.toBits))) +
        (value s.1.toBits + value s.2.toBits -
          (value l1x.toBits + value l2x.toBits + (value l0xl.toBits + value l1xl.toBits))) +
        (value l0xl.toBits - (value l0m.toBits * W - value l0x.toBits)) +
        (value l1xl.toBits - (a1 * W - value l1x.toBits))) (value l2x.toBits - a2 * W)
    have a5 := abs_add_le
      ((t1 + t2 - (value s.1.toBits + value s.2.toBits + (value p0.toBits + value p1.toBits))) +
        (value s.1.toBits + value s.2.toBits -
          (value l1x.toBits + value l2x.toBits + (value l0xl.toBits + value l1xl.toBits))) +
        (value l0xl.toBits - (value l0m.toBits * W - value l0x.toBits)))
      (value l1xl.toBits - (a1 * W - value l1x.toBits))
    have a6 := abs_add_le
      ((t1 + t2 - (value s.1.toBits + value s.2.toBits + (value p0.toBits + value p1.toBits))) +
        (value s.1.toBits + value s.2.toBits -
          (value l1x.toBits + value l2x.toBits + (value l0xl.toBits + value l1xl.toBits))))
      (value l0xl.toBits - (value l0m.toBits * W - value l0x.toBits))
    have a7 := abs_add_le
      (t1 + t2 - (value s.1.toBits + value s.2.toBits + (value p0.toBits + value p1.toBits)))
      (value s.1.toBits + value s.2.toBits -
        (value l1x.toBits + value l2x.toBits + (value l0xl.toBits + value l1xl.toBits)))
    linarith
  · have h := hx0.2
    rw [hmv] at h
    linarith [(by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000)] :
      (1 : ℝ) / 2 ^ 1075 ≤ W / 2 ^ 53), (by ring : 84 * W / 2 ^ 53 = 83 * W / 2 ^ 53 + W / 2 ^ 53)]
  · have h1 : |t1| / 2 ^ 51 ≤ W / 2 ^ 40 / 2 ^ 51 := div_le_div_of_nonneg_right ht1b (by norm_num)
    have : W / 2 ^ 87 * (1 + 1 / 2 ^ 51) + W / 2 ^ 40 / 2 ^ 51 + W / 2 ^ 1000 ≤ W / 2 ^ 86 := by
      have : W / 2 ^ 87 * (1 + 1 / 2 ^ 51) + W / 2 ^ 40 / 2 ^ 51 + W / 2 ^ 1000 =
          W * (1 / 2 ^ 87 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 40 / 2 ^ 51 + 1 / 2 ^ 1000) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 87 * (1 + 1 / 2 ^ 51) +
        1 / 2 ^ 40 / 2 ^ 51 + 1 / 2 ^ 1000 ≤ 1 / 2 ^ 86) hW0.le
      linarith [(by ring : W * (1 / 2 ^ 86) = W / 2 ^ 86)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1073 ≤ 1 / 2 ^ 1075 * 4), hη]

#print axioms prod_spec

end Verified.Examples.LgammaAsymProd
