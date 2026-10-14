import Verified.Examples.LgammaRootEval

/-!
The code of `Lgamma.accurate` for one range of the polynomials about the negative zeros, before
the polynomial: the shifted argument `z = sx + x0` from the triple `e0 + e1 + e2` of `-x0`
(`z_spec`).  `e0 + sx` is exact by Sterbenz's lemma, since `sx` lies within `1/2` of `-e0`.
Both lie in the binade `[2^p, 2^(p+1))` and are multiples of `2^(p - 52)`, so `e0 + sx` is zero or
at least `2^(p - 52)`, and `fastTwoSum` with `|e1| ≤ 2^(p - 53)` is exact.  The low part then
takes `e2` with one rounding, and `zh + zl` is within `|z|/2^71` of `z` for `|z| ≥ 2^-80`.
-/

namespace Verified.Examples.LgammaRootPath
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD LgammaAccLow LgammaAccAdd

set_option exponentiation.threshold 4096

/-- `add a b` is `sub a (negate b)`. -/
theorem add_eq_sub (a b : UInt64) :
    Wasm.IEEE64.add a b = Wasm.IEEE64.sub a (Wasm.IEEE64.negate b) := by
  rw [show Wasm.IEEE64.sub a (Wasm.IEEE64.negate b) =
    Wasm.IEEE64.add a (Wasm.IEEE64.negate (Wasm.IEEE64.negate b)) from rfl,
    F64RelativeStep.negate_negate]

/-- **Sterbenz's lemma for a sum** of operands of opposite signs. -/
theorem add_sterbenz (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (h1 : |value a.toBits + value b.toBits| ≤ |value a.toBits|)
    (h2 : |value a.toBits + value b.toBits| ≤ |value b.toBits|)
    (h3 : |value b.toBits| < 2 ^ 1021) :
    Finite (a + b).toBits ∧ value (a + b).toBits = value a.toBits + value b.toBits := by
  obtain ⟨hnb, hnbv⟩ := F64Magnitude.negate_value b.toBits hb
  rw [F64Bits.toBits_add, add_eq_sub]
  obtain ⟨hf, hv⟩ := F64Sterbenz.sub_exact a.toBits (Wasm.IEEE64.negate b.toBits) ha hnb
    (by rw [hnbv, sub_neg_eq_add]; exact h1)
    (by rw [hnbv, sub_neg_eq_add, abs_neg]; exact h2)
    (by rw [hnbv, abs_neg]; exact h3)
  rw [hnbv, sub_neg_eq_add] at hv
  exact ⟨hf, hv⟩

/-- A double of magnitude at least `2^p` is a multiple of `2^(p - 52)`. -/
theorem grid_p (w : UInt64) (hw : Finite w) (p : ℕ) (hp : p ≤ 1000)
    (h : (2 : ℝ) ^ p ≤ |value w|) : ∃ K : ℤ, value w = K * 2 ^ p / 2 ^ 52 := by
  obtain ⟨K, hK⟩ := TgammaMainRed.grid w hw (p + 1021) (by omega)
    (by rw [show (2 : ℝ) ^ (53 + (p + 1021)) / 2 ^ 1074 = 2 ^ p by
          rw [show 53 + (p + 1021) = p + 1074 by omega, pow_add]; field_simp]
        exact h)
  refine ⟨K, ?_⟩
  have e : (2 : ℝ) ^ (p + 1021 + 1) = 2 ^ p * 2 ^ 1022 := by rw [← pow_add]
  rw [e] at hK
  have h1074 : (2 : ℝ) ^ 1074 = 2 ^ 52 * 2 ^ 1022 := by norm_num
  field_simp
  rw [h1074] at hK
  nlinarith [hK]

set_option maxHeartbeats 4000000 in
/-- **The shifted argument** `zh + zl ≈ sx + e0 + e1 + e2`. -/
theorem z_spec (e0 e1 e2 sx : Float) (h0 : Finite e0.toBits) (h1 : Finite e1.toBits)
    (h2 : Finite e2.toBits) (hsx : Finite sx.toBits) (p : ℕ) (hp : p ≤ 10)
    (he0 : (2 : ℝ) ^ p ≤ value e0.toBits) (hsx1 : (2 : ℝ) ^ p ≤ -value sx.toBits)
    (hsx2 : -value sx.toBits < 2 ^ (p + 1))
    (hnear : |value e0.toBits + value sx.toBits| ≤ 1 / 2)
    (he1 : |value e1.toBits| ≤ 2 ^ p / 2 ^ 53) (he2 : |value e2.toBits| ≤ 1 / 2 ^ 100)
    (hz : 1 / 2 ^ 80 ≤ |value sx.toBits + (value e0.toBits + value e1.toBits + value e2.toBits)|)
    (zh zl : Float) (hT : fastTwoSum (e0 + sx) e1 = (zh, zl)) :
    Finite zh.toBits ∧ Finite (zl + e2).toBits ∧
      |value zh.toBits + value (zl + e2).toBits -
          (value sx.toBits + (value e0.toBits + value e1.toBits + value e2.toBits))| ≤
        |value sx.toBits + (value e0.toBits + value e1.toBits + value e2.toBits)| / 2 ^ 71 ∧
      |value (zl + e2).toBits| ≤ |value zh.toBits| / 2 ^ 51 + 1 / 2 ^ 99 ∧
      |value zh.toBits| ≤ 1 := by
  have hpp : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have hp11 : (2 : ℝ) ^ (p + 1) ≤ 2 ^ 11 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hp10 : (2 : ℝ) ^ p ≤ 2 ^ 10 := pow_le_pow_right₀ (by norm_num) hp
  have hsxn : value sx.toBits < 0 := by linarith
  -- `e0 + sx` is exact
  obtain ⟨af, av⟩ := add_sterbenz e0 sx h0 hsx
    (by rw [abs_of_pos (show (0 : ℝ) < value e0.toBits by linarith)]; linarith [abs_le.mp hnear])
    (by rw [abs_of_neg hsxn]; linarith [abs_le.mp hnear])
    (by rw [abs_of_neg hsxn]; linarith [(by norm_num : (2 : ℝ) ^ 11 < 2 ^ 1021)])
  -- the grid of the binade
  obtain ⟨K0, hK0⟩ := grid_p e0.toBits h0 p (by omega)
    (by rw [abs_of_pos (show (0 : ℝ) < value e0.toBits by linarith)]; exact he0)
  obtain ⟨K1, hK1⟩ := grid_p sx.toBits hsx p (by omega) (by rw [abs_of_neg hsxn]; exact hsx1)
  have hsum : value e0.toBits + value sx.toBits = ((K0 + K1 : ℤ) : ℝ) * 2 ^ p / 2 ^ 52 := by
    rw [hK0, hK1]; push_cast; ring
  -- the exact two-sum of `e0 + sx` and `e1`
  obtain ⟨zf, lf, hzs, hzl⟩ : Finite zh.toBits ∧ Finite zl.toBits ∧
      value zh.toBits + value zl.toBits = value e0.toBits + value sx.toBits + value e1.toBits ∧
      |value zl.toBits| ≤ |value zh.toBits| / 2 ^ 52 + 1 / 2 ^ 1074 := by
    by_cases hK : K0 + K1 = 0
    · have ha0 : value (e0 + sx).toBits = 0 := by rw [av, hsum, hK]; simp
      obtain ⟨f1, f2, v1, v2⟩ := LgammaLogdAcc.fts_zero (e0 + sx) e1 af h1 ha0
        (by linarith [abs_nonneg (value e1.toBits), (by norm_num : (2 : ℝ) ^ 10 / 2 ^ 53 < 2 ^ 1000),
          div_le_div_of_nonneg_right hp10 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)])
      rw [hT] at f1 f2 v1 v2
      dsimp only at f1 f2 v1 v2
      refine ⟨f1, f2, by rw [v1, v2, ← av, ha0]; ring, by rw [v2, abs_zero]; positivity⟩
    · have hK1' : (1 : ℝ) ≤ |((K0 + K1 : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hK
      have hge : 2 ^ p / 2 ^ 52 ≤ |value e0.toBits + value sx.toBits| := by
        rw [hsum, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ p),
          abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 52)]
        rw [div_le_div_iff_of_pos_right (by positivity)]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) p]
      have hle : |value e1.toBits| ≤ 2 ^ p / 2 ^ 52 := by
        have : (2 : ℝ) ^ p / 2 ^ 53 ≤ 2 ^ p / 2 ^ 52 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by norm_num)
        linarith
      obtain ⟨f1, f2, v1, -, v2⟩ := fastTwoSum_spec (e0 + sx) e1 af h1
        (by rw [av]; linarith)
        (by rw [av]; linarith [(by norm_num : (1 : ℝ) / 2 < 2 ^ 900), abs_le.mp hnear])
      rw [hT] at f1 f2 v1 v2
      dsimp only at f1 f2 v1 v2
      exact ⟨f1, f2, by rw [v1, av], v2⟩
  set z := value sx.toBits + (value e0.toBits + value e1.toBits + value e2.toBits) with hzdef
  -- the high part
  have hzh : |value zh.toBits| ≤ |z| * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 99 := by
    have h3 := abs_sub_abs_le_abs_sub (value zh.toBits) (z - value e2.toBits)
    rw [show value zh.toBits - (z - value e2.toBits) = -value zl.toBits by rw [hzdef]; linarith,
      abs_neg] at h3
    have := abs_sub z (value e2.toBits)
    have := abs_nonneg z
    nlinarith
  have hzh1 : |value zh.toBits| ≤ 1 := by
    have : |z| ≤ 1 / 2 + 2 ^ p / 2 ^ 53 + 1 / 2 ^ 100 := by
      rw [hzdef, show value sx.toBits + (value e0.toBits + value e1.toBits + value e2.toBits) =
        (value e0.toBits + value sx.toBits) + value e1.toBits + value e2.toBits by ring]
      have := abs_add_le (value e0.toBits + value sx.toBits + value e1.toBits) (value e2.toBits)
      have := abs_add_le (value e0.toBits + value sx.toBits) (value e1.toBits)
      linarith
    have := div_le_div_of_nonneg_right hp10 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)
    nlinarith [(by norm_num : ((1 : ℝ) / 2 + 2 ^ 10 / 2 ^ 53 + 1 / 2 ^ 100) * (1 + 1 / 2 ^ 51) +
      1 / 2 ^ 99 ≤ 1), abs_nonneg z]
  have hzl1 : |value zl.toBits| ≤ 1 / 2 ^ 51 := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 51),
      div_le_div_of_nonneg_right hzh1 (by norm_num : (0 : ℝ) ≤ 2 ^ 52)]
  have hr := fapprox_add (fapprox_self zl lf) (fapprox_self e2 h2)
    (|value zl.toBits| + |value e2.toBits|) (by simp only [add_zero]; exact abs_add_le _ _)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 51 + 1 / 2 ^ 100 < 2 ^ 1023)])
  obtain ⟨rf, re⟩ := hr
  simp only [zero_add] at re
  refine ⟨zf, rf, ?_, ?_, hzh1⟩
  · have k : value zh.toBits + value (zl + e2).toBits - z =
        value (zl + e2).toBits - (value zl.toBits + value e2.toBits) := by
      rw [hzdef]; linarith
    rw [k]
    have h80 : (1 : ℝ) / 2 ^ 152 ≤ |z| / 2 ^ 72 := by
      have := div_le_div_of_nonneg_right hz (by norm_num : (0 : ℝ) ≤ 2 ^ 72)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 152 ≤ 1 / 2 ^ 80 / 2 ^ 72)]
    have hzl' : |value zl.toBits| ≤ |z| / 2 ^ 51 + 1 / 2 ^ 150 := by
      have := div_le_div_of_nonneg_right hzh (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
      have := abs_nonneg z
      nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 99 / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 150)]
    have : (|value zl.toBits| + |value e2.toBits|) / 2 ^ 53 ≤ |z| / 2 ^ 104 + 1 / 2 ^ 152 := by
      have h3 : |value zl.toBits| + |value e2.toBits| ≤ |z| / 2 ^ 51 + 1 / 2 ^ 99 := by
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 150 + 1 / 2 ^ 100 ≤ 1 / 2 ^ 99)]
      have := div_le_div_of_nonneg_right h3 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 99 / 2 ^ 53 = 1 / 2 ^ 152)]
    have : |z| / 2 ^ 104 + |z| / 2 ^ 72 ≤ |z| / 2 ^ 71 := by
      have := abs_nonneg z
      linarith
    linarith
  · have h3 := abs_sub_abs_le_abs_sub (value (zl + e2).toBits) (value zl.toBits + value e2.toBits)
    have h4 := abs_add_le (value zl.toBits) (value e2.toBits)
    have h5 : (|value zl.toBits| + |value e2.toBits|) / 2 ^ 53 ≤ (1 / 2 ^ 51 + 1 / 2 ^ 100) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : ((1 : ℝ) / 2 ^ 51 + 1 / 2 ^ 100) / 2 ^ 53 + 1 / 2 ^ 1074 + 1 / 2 ^ 100 ≤
      1 / 2 ^ 99), abs_nonneg (value zh.toBits)]

#print axioms add_sterbenz
#print axioms grid_p
#print axioms z_spec

end Verified.Examples.LgammaRootPath
